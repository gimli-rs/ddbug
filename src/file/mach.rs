use object::{self, Object};

use Result;
use file::File;

pub(crate) fn parse(
    input: &[u8],
    path: &str,
    cb: &mut FnMut(&mut File) -> Result<()>,
) -> Result<()> {
    let object = object::MachOFile::parse(&input)?;
    let mut file = File {
        path,
        ..Default::default()
    };
    file.parse_object(&object)?;
    file.normalize();
    cb(&mut file)
}
