pub trait Endian {
    fn to_bytes(res: &mut [u8], el: &[u64]);
    fn from_bytes(res: &[u8], el: &mut [u64]);
}

pub struct LE;
pub struct BE;

impl Endian for LE {
    fn to_bytes(res: &mut [u8], el: &[u64]) {
        el.iter().enumerate().for_each(|(i, limb)| {
            let off = i * 8;
            res[off..off + 8].copy_from_slice(&limb.to_le_bytes());
        });
    }

    fn from_bytes(res: &[u8], el: &mut [u64]) {
        el.iter_mut().enumerate().for_each(|(i, limb)| {
            let off = i * 8;
            *limb = u64::from_le_bytes(res[off..off + 8].try_into().unwrap());
        });
    }
}
impl Endian for BE {
    fn to_bytes(res: &mut [u8], el: &[u64]) {
        el.iter().rev().enumerate().for_each(|(i, limb)| {
            let off = i * 8;
            res[off..off + 8].copy_from_slice(&limb.to_be_bytes());
        });
    }

    fn from_bytes(res: &[u8], el: &mut [u64]) {
        el.iter_mut().rev().enumerate().for_each(|(i, limb)| {
            let off = i * 8;
            *limb = u64::from_be_bytes(res[off..off + 8].try_into().unwrap());
        });
    }
}

pub trait FieldRepr: Sized {
    const SIZE: usize;

    type Repr: Copy + Default + Send + Sync + 'static + AsRef<[u8]> + AsMut<[u8]>;

    fn from_repr<E: Endian>(repr: &Self::Repr) -> subtle::CtOption<Self>;
    fn to_repr<E: Endian>(&self) -> Self::Repr;

    fn read_repr<E: Endian, R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut repr = Self::Repr::default();
        reader.read_exact(repr.as_mut())?;

        Option::<Self>::from(Self::from_repr::<E>(&repr)).ok_or(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Invalid field element",
        ))
    }

    fn write_repr<E: Endian, W: std::io::Write>(&self, writer: &mut W) {
        let repr = self.to_repr::<E>();
        writer.write_all(repr.as_ref()).unwrap();
    }
}

pub trait FieldReprRaw: FieldRepr {
    fn from_raw_repr<E: Endian>(repr: &Self::Repr) -> subtle::CtOption<Self>;
    fn from_raw_repr_unchecked<E: Endian>(repr: &Self::Repr) -> subtle::CtOption<Self>;
    fn to_raw_repr<E: Endian>(&self) -> Self::Repr;

    fn read_raw_repr<E: Endian, R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut repr = Self::Repr::default();
        reader.read_exact(repr.as_mut())?;

        Option::<Self>::from(Self::from_raw_repr::<E>(&repr)).ok_or(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Invalid field element",
        ))
    }

    fn read_raw_repr_unchecked<E: Endian, R: std::io::Read>(
        reader: &mut R,
    ) -> std::io::Result<Self> {
        let mut repr = Self::Repr::default();
        reader.read_exact(repr.as_mut())?;
        Option::<Self>::from(Self::from_raw_repr_unchecked::<E>(&repr)).ok_or(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Invalid field element",
        ))
    }

    fn write_raw_repr<E: Endian, W: std::io::Write>(&self, writer: &mut W) {
        let repr = self.to_raw_repr::<E>();
        writer.write_all(repr.as_ref()).unwrap();
    }
}
