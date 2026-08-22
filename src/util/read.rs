use std::{io, io::Read};

use zerocopy::{FromBytes, FromZeros, IntoBytes};

#[inline(always)]
pub fn read_from<T, R>(reader: &mut R) -> io::Result<T>
where
    T: FromBytes + IntoBytes,
    R: Read + ?Sized,
{
    let mut ret = <T>::new_zeroed();
    reader.read_exact(ret.as_mut_bytes())?;
    Ok(ret)
}

#[inline(always)]
pub fn read_box_slice<T, R>(reader: &mut R, count: usize) -> io::Result<Box<[T]>>
where
    T: FromBytes + IntoBytes,
    R: Read + ?Sized,
{
    let mut ret = <[T]>::new_box_zeroed_with_elems(count)
        .map_err(|_| io::Error::from(io::ErrorKind::OutOfMemory))?;
    reader.read_exact(ret.as_mut().as_mut_bytes())?;
    Ok(ret)
}

// quick and ez ways to read data from a block of bytes
pub fn read_halfword(data: &[u8], index: usize) -> u16 {
    u16::from_be_bytes([data[index], data[index + 1]])
}

pub fn read_word(data: &[u8], index: usize) -> u32 {
    u32::from_be_bytes([
        data[index],
        data[index + 1],
        data[index + 2],
        data[index + 3],
    ])
}
