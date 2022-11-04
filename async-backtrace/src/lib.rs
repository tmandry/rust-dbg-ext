use anyhow::anyhow;
use gimli::{AttributeValue, EvaluationResult, Location, Piece, UnitOffset};
use std::{
    borrow::Cow,
    collections::VecDeque,
    ffi::c_void,
    fmt::Write,
    fs,
    future::Future,
    mem::{self, MaybeUninit},
    ptr::slice_from_raw_parts,
};

type Byte = MaybeUninit<u8>;

pub fn trace<F: Future + ?Sized>(fut: &F) {
    let Some(ip) = __async_backtrace_trace_internal(fut) else { return };
    let fut_bytes = slice_from_raw_parts(fut as *const F as *const Byte, mem::size_of_val(fut));
    // SAFETY: fut_bytes is a slice of bytes coming from a valid value of the
    // type of the future passed to __async_backtrace_trace_internal. We use
    // MaybeUninit in the value type because the slice could contain padding.
    let fut_bytes = unsafe { &*fut_bytes };
    match unsafe { perform_trace(ip, fut_bytes) } {
        Ok(()) => (),
        Err(e) => eprintln!("Failed to trace future: {:?}", e),
    }
}

fn current_binary() -> Option<fs::File> {
    let path = std::env::args_os().skip(1).next()?;
    let file = fs::File::open(&dbg!(path)).ok()?;
    Some(file)
}

// SAFTEY: `ip` must be a code address from __async_backtrace_trace_internal
// invoked with a future of some type `F`, of which `fut` is a valid value.
unsafe fn perform_trace(ip: *mut c_void, fut: &[Byte]) -> anyhow::Result<()> {
    dbg!(ip);
    let file = current_binary().ok_or(anyhow!("Could not open current binary"))?;
    let mmap = unsafe { memmap2::Mmap::map(&file).unwrap() };
    let object = object::File::parse(&*mmap)?;
    let ctx = addr2line::Context::new(&object)?;
    let dwarf = ctx.dwarf();

    let mut frames = ctx.find_frames(ip as u64)?;
    eprintln!("frames:");
    while let Some(frame) = frames.next()? {
        eprintln!(
            "{:?} {:?} {:?}",
            frame.function.map(|f| f.demangle().map(Cow::into_owned)),
            frame.location.and_then(|l| l.file),
            frame.dw_die_offset
        );
    }
    eprintln!("location:");
    let loc = ctx.find_location(ip as u64)?.unwrap();
    eprintln!("{:?} {:?} {:?}", loc.file, loc.line, loc.column);

    let dw_die_offset = ctx
        .find_frames(ip as u64)?
        .next()?
        .and_then(|f| f.dw_die_offset)
        .ok_or(anyhow!(
            "Could not find debug information for internal trace function"
        ))?;
    let unit = ctx.find_dwarf_unit(ip as u64).unwrap();

    let mut ty = None;
    let mut tree = unit.entries_tree(Some(dw_die_offset))?;
    //inspect_tree(&mut tree, dwarf, unit)?;
    let mut children = tree.root()?.children();
    while let Some(child) = children.next()? {
        if ty.is_none() && child.entry().tag() == gimli::DW_TAG_formal_parameter {
            ty = get_type(child.entry())?;
        }
    }
    let ty = ty.ok_or(anyhow!("Could not find parameter type entry"))?;

    crawl_type(unit, ty, dwarf, fut)?;

    Ok(())
}

fn crawl_type<R: gimli::Reader<Offset = usize> + PartialEq>(
    unit: &gimli::Unit<R>,
    ptr_ty: UnitOffset,
    dwarf: &gimli::Dwarf<R>,
    fut: &[Byte],
) -> Result<(), anyhow::Error> {
    let fut_ty = {
        inspect_tree(&mut unit.entries_tree(Some(ptr_ty))?, dwarf, unit)?;
        let ptr_entry = unit.entry(ptr_ty)?;
        let Some(fut_ty) = get_type(&ptr_entry)? else {
            return Err(anyhow!("Expected pointer type"));
        };
        let fut_entry = unit.entry(fut_ty)?;
        assert_eq!(
            fut.len(),
            fut_entry
                .attr_value(gimli::DW_AT_byte_size)?
                .and_then(|s| s.udata_value())
                .ok_or(anyhow!("Missing size attribute on primary future type"))?
                .try_into()
                .unwrap(),
        );
        let align: usize = fut_entry
            .attr_value(gimli::DW_AT_alignment)?
            .and_then(|s| s.udata_value())
            .ok_or(anyhow!("Missing size attribute on primary future type"))?
            .try_into()
            .unwrap();
        assert!((fut.as_ptr() as usize) % align == 0);
        fut_ty
    };

    #[derive(Copy, Clone, Debug)]
    enum AwaiteeState {
        None,
        IsGeneratorVariant,
        IsAwaitee,
    }

    let mut queue = VecDeque::new();
    queue.push_back((0, fut_ty, fut.as_ptr(), None, AwaiteeState::None));

    while let Some((depth, ty, ptr, parent_ty, awaitee)) = queue.pop_back() {
        let entry = unit.entry(ty)?;
        eprintln!(
            "{blk:depth$}{} at {:?}",
            entry
                .attr(gimli::DW_AT_name)?
                .map(|attr| -> Result<String, anyhow::Error> {
                    Ok(dwarf
                        .attr_string(&unit, attr.value())?
                        .to_string_lossy()?
                        // Not sure why this is needed
                        .into_owned())
                })
                .transpose()?
                .unwrap_or("<unnamed type>".into()),
            ptr,
            blk = "",
        );

        let mut tree = unit.entries_tree(Some(ty))?;
        inspect_tree(&mut tree, dwarf, unit)?;

        if let Some(pointee) = get_type(&entry)? {
            if entry.tag() == gimli::DW_TAG_pointer_type {
                let target = unsafe { *(ptr as *const *const Byte) };
                queue.push_back((depth + 1, pointee, target, Some(ty), awaitee));
            } else {
                // Can remove this and invert the conditions if we don't find
                // anything interesting.
                eprintln!(
                    "Warning: Found type designation of unknown non-pointer tag {}",
                    entry.tag()
                );
            }
        }

        let eval_addr = |attr: AttributeValue<R>, start| -> Result<_, anyhow::Error> {
            if let Some(loc) = attr.exprloc_value() {
                // TODO: We probably don't need full evaluation here and can
                // just support PlusConstant.
                let mut eval = loc.evaluation(unit.encoding());
                eval.set_initial_value(start);
                if EvaluationResult::Complete == eval.evaluate()? {
                    let result = eval.result();
                    match result[..] {
                        [Piece {
                            size_in_bits: None,
                            bit_offset: None,
                            location: Location::Address { address },
                        }] => return Ok(Some(address)),
                        _ => eprintln!("Warning: Unsupported evaluation result {:?}", result,),
                    }
                } else if let AttributeValue::Udata(offset) = attr {
                    return Ok(Some(start + offset))
                }
            }
            Ok(None)
        };

        let mut children = tree.root()?.children();
        while let Some(child) = children.next()? {
            match child.entry().tag() {
                gimli::DW_TAG_member => {
                    if let Some(attr) = child
                        .entry()
                        .attr_value(gimli::DW_AT_data_member_location)?
                    {
                        let Some(field_ty) = get_type(&child.entry())? else {
                            eprintln!("Warning: Data member {:?} missing a type", child.entry());
                            continue;
                        };
                        if let Some(address) = eval_addr(attr, ptr as u64)? {
                            queue.push_front((
                                depth + 1,
                                field_ty,
                                address as *const _,
                                Some(ty),
                                match awaitee {
                                    AwaiteeState::IsGeneratorVariant => {
                                        if let Some(name) = get_name(child.entry(), dwarf, unit)? {
                                            if let Some("__awaitee") =
                                                name.to_string().ok().as_deref()
                                            {
                                                AwaiteeState::IsAwaitee
                                            } else {
                                                AwaiteeState::None
                                            }
                                        } else {
                                            AwaiteeState::None
                                        }
                                    }
                                    AwaiteeState::None | AwaiteeState::IsAwaitee => awaitee,
                                },
                            ));
                        }
                    }
                }
                gimli::DW_TAG_variant_part => {
                    let mut discr_value: Option<u64> = None;
                    let mut discr_found = false;
                    let mut children = child.children();
                    while let Some(child) = children.next()? {
                        match child.entry().tag() {
                            gimli::DW_TAG_member => {
                                // TODO support niches
                                let Some(name) = get_name(child.entry(), dwarf, unit)? else { continue };
                                let Some(name) = name.to_string().ok() else { continue };
                                let Some(loc) = child.entry().attr_value(gimli::DW_AT_data_member_location)? else {
                                    continue
                                };
                                if name != "__state" {
                                    continue;
                                }
                                if discr_value.is_some() {
                                    return Err(anyhow!("Multiple discriminants found"));
                                }
                                let Some(ty) = get_type(child.entry())? else { continue };
                                // rejoice!
                                eprintln!("discr: {name}");
                                inspect_entry(&unit.entry(ty)?, dwarf, unit, 0)?;
                                let Some(_align) = child
                                    .entry()
                                    .attr_value(gimli::DW_AT_alignment)?
                                    .or(unit.entry(ty)?.attr_value(gimli::DW_AT_alignment)?) else {
                                        continue
                                    };
                                let (Some(size), Some(encoding)) = (
                                    unit.entry(ty)?.attr_value(gimli::DW_AT_byte_size)?,
                                    unit.entry(ty)?.attr_value(gimli::DW_AT_encoding)?,
                                ) else { continue };
                                let AttributeValue::Encoding(gimli::DW_ATE_unsigned) = encoding else {
                                    eprintln!("Warning: Unknown encoding {encoding:?} for discriminant");
                                    continue;
                                };
                                let Some(addr) = eval_addr(loc, ptr as u64)? else { continue };
                                match size.udata_value() {
                                    Some(1) => {
                                        let addr = dbg!(addr as *const u8);
                                        discr_value = Some(unsafe { *addr }.into());
                                    }
                                    _ => {
                                        // TODO
                                    }
                                }
                                dbg!(discr_value);
                            }
                            gimli::DW_TAG_variant if discr_value.is_some() => {
                                let Some(variant_discr) = child.entry().attr_value(gimli::DW_AT_discr_value)? else { continue };
                                if discr_value != variant_discr.udata_value() {
                                    continue;
                                }
                                if discr_found {
                                    return Err(anyhow!(
                                        "Multiple variants found with discr value {}",
                                        discr_value.unwrap()
                                    ));
                                }
                                discr_found = true;

                                // There should only be one child and it should be a member.
                                // We'll use this member to get the name of the variant.
                                let mut children = child.children();
                                let Some(variant_child) = children.next()? else { continue };
                                if gimli::DW_TAG_member != variant_child.entry().tag() {
                                    eprintln!(
                                        "Warning: Unexpected child of variant: {:?}",
                                        variant_child.entry().tag()
                                    );
                                    continue;
                                }

                                let Some(variant_type) = get_type(variant_child.entry())? else {
                                    eprintln!("Warning: Missing type of variant {:?}", variant_child.entry().offset());
                                    continue;
                                };

                                let Some(variant_name) = get_name(&unit.entry(variant_type)?, dwarf, unit)? else { continue };
                                let variant_name = variant_name.to_string_lossy()?;

                                let Some(parent_ty) = parent_ty else { continue };
                                let Some(parent_ty_name) = get_name(&unit.entry(parent_ty)?, dwarf, unit)? else { continue };
                                let parent_ty_name = parent_ty_name.to_string_lossy()?;

                                let decl_file =
                                    variant_child.entry().attr_value(gimli::DW_AT_decl_file)?;
                                let decl_line =
                                    variant_child.entry().attr_value(gimli::DW_AT_decl_line)?;
                                let decl_col =
                                    variant_child.entry().attr_value(gimli::DW_AT_decl_column)?;

                                let state_desc = if let (Some(file), Some(line)) =
                                    (decl_file, decl_line.and_then(|l| l.udata_value()))
                                {
                                    let mut desc = format!("at {file:?}:{line}");
                                    if let Some(col) = decl_col.and_then(|c| c.udata_value()) {
                                        write!(&mut desc, ":{}", col)?;
                                    }
                                    desc
                                } else {
                                    format!("")
                                };

                                println!(
                                    "{blk:depth$}{star} ({ptr:?}) {parent_ty_name} in state {variant_name} {state_desc}",
                                    blk = "",
                                    star = if let AwaiteeState::IsAwaitee = awaitee { "*" } else { " " },
                                );

                                let Some(variant_addr) = variant_child
                                    .entry()
                                    .attr_value(gimli::DW_AT_data_member_location)? else { continue };
                                let Some(variant_addr) = eval_addr(variant_addr, ptr as _)? else { continue };
                                queue.push_back((
                                    depth + 1,
                                    variant_type,
                                    variant_addr as _,
                                    Some(parent_ty),
                                    AwaiteeState::IsGeneratorVariant,
                                )); // parent_ty??

                                if let Some(next_child) = children.next()? {
                                    eprintln!(
                                        "Warning: Unexpected child of variant: {:?}",
                                        next_child.entry().tag()
                                    );
                                    continue;
                                }
                            }
                            _ => (),
                        }
                    }

                    // These could possibly be warnings instead of errors.
                    if !discr_value.is_some() {
                        return Err(anyhow!("No discriminant found in variant part"));
                    }
                    if !discr_found {
                        return Err(anyhow!(
                            "No match for discriminant value {} found",
                            discr_value.unwrap()
                        ));
                    }
                }
                _ => (),
            }
        }
    }

    Ok(())
}

fn get_name<R: gimli::Reader<Offset = usize>>(
    entry: &gimli::DebuggingInformationEntry<R>,
    dwarf: &gimli::Dwarf<R>,
    unit: &gimli::Unit<R, usize>,
) -> anyhow::Result<Option<R>> {
    let Some(name) = entry.attr_value(gimli::DW_AT_name)? else { return Ok(None) };
    let name = dwarf.attr_string(&unit, name)?;
    Ok(Some(name))
}

fn get_type<R: gimli::Reader<Offset = usize>>(
    entry: &gimli::DebuggingInformationEntry<R>,
) -> Result<Option<UnitOffset>, anyhow::Error> {
    get_attr_ref(entry, gimli::DW_AT_type)
}

fn get_attr_ref<R: gimli::Reader<Offset = usize>>(
    entry: &gimli::DebuggingInformationEntry<R>,
    name: gimli::DwAt,
) -> Result<Option<UnitOffset>, anyhow::Error> {
    if let Some(attr) = entry.attr(name)? {
        if let AttributeValue::UnitRef(offset) = attr.value() {
            return Ok(Some(offset));
        }
    }
    Ok(None)
}

fn inspect_tree<R: gimli::Reader<Offset = usize>>(
    tree: &mut gimli::EntriesTree<R>,
    dwarf: &gimli::Dwarf<R>,
    unit: &gimli::Unit<R>,
) -> Result<(), anyhow::Error> {
    inspect_tree_node(tree.root()?, dwarf, unit, 0)
}

fn inspect_tree_node<R: gimli::Reader<Offset = usize>>(
    node: gimli::EntriesTreeNode<R>,
    dwarf: &gimli::Dwarf<R>,
    unit: &gimli::Unit<R>,
    depth: isize,
) -> Result<(), anyhow::Error> {
    inspect_entry(node.entry(), dwarf, unit, depth)?;
    let mut children = node.children();
    Ok(while let Some(child) = children.next()? {
        inspect_tree_node(child, dwarf, unit, depth + 1)?;
    })
}

fn inspect_entry<R: gimli::Reader<Offset = usize>>(
    entry: &gimli::DebuggingInformationEntry<R, usize>,
    dwarf: &gimli::Dwarf<R>,
    unit: &gimli::Unit<R>,
    depth: isize,
) -> Result<(), anyhow::Error> {
    let indent = (depth * 4).try_into().unwrap_or(0);
    eprintln!(
        "{:indent$} <{offset}> {tag}",
        "",
        offset = entry.offset().0,
        tag = entry.tag()
    );
    let mut attrs = entry.attrs();
    Ok(while let Some(attr) = attrs.next()? {
        match dwarf.attr_string(&unit, attr.value()) {
            Ok(r) => {
                let val = r.to_string_lossy()?;
                match &*attr.name().to_string() {
                    "DW_AT_MIPS_linkage_name" => {
                        let val = rustc_demangle::demangle(&val);
                        eprintln!("{:indent$}    {}: {:?}", "", attr.name(), val)
                    }
                    _ => eprintln!("{:indent$}    {}: {:?}", "", attr.name(), val),
                }
            }

            _ if attr.exprloc_value().is_some() => {
                eprint!("{:indent$}    {} [", "", attr.name());
                let mut ops = attr.exprloc_value().unwrap().operations(unit.encoding());
                while let Some(op) = ops.next()? {
                    eprint!("{op:?}, ");
                }
                eprintln!("]");
            }
            _ => eprintln!("{:indent$}    {}: {:?}", "", attr.name(), attr.value()),
        }
    })
}

#[inline(never)]
fn __async_backtrace_trace_internal<F: Future + ?Sized>(_fut: &F) -> Option<*mut c_void> {
    // TODO: This can be optimized with lower level APIs in backtrace.
    let backtrace = backtrace::Backtrace::new();
    eprintln!("{backtrace:?}");
    for frame in backtrace.frames() {
        for symbol in frame.symbols() {
            if symbol
                .name()
                .and_then(|n| n.as_str())
                .map(|n| n.contains("__async_backtrace_trace_internal"))
                .unwrap_or(false)
            {
                return symbol.addr();
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
