use crate::{
    Trits,
    TritsMut,
    TritsBuf,
    i384::{
        BigEndian,
        LittleEndian,
    },
};

pub trait Sealed {}

impl<'a> Sealed for Trits<'a> {}
impl<'a> Sealed for TritsMut<'a> {}
impl Sealed for TritsBuf {}

impl Sealed for BigEndian {}
impl Sealed for LittleEndian {}
