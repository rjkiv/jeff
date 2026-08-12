use std::{
    fs::File,
    io::{BufReader, Read},
};

use anyhow::{ensure, Result};
use argp::FromArgs;
use typed_path::Utf8NativePathBuf;

use crate::util::path::native_path;

/// Command for extracting the achievement icons and gamerpics from XEXs or EXEs.
/// Or anything else with embedded PNGs.
#[derive(FromArgs, PartialEq, Debug)]
#[argp(subcommand, name = "pngs")]
pub struct Args {
    #[argp(positional, from_str_fn(native_path))]
    /// XEX or EXE to extract PNGs from.
    file: Utf8NativePathBuf,
}

pub fn run(args: Args) -> Result<()> {
    let file_name = args.file.file_stem();
    ensure!(file_name.is_some(), "Need to provide a named file!");

    let cwd = args.file.parent().unwrap();
    let out_dir = cwd.join(file_name.unwrap().to_string() + "_pngs");
    std::fs::create_dir_all(&out_dir).unwrap();

    read_other(args.file, out_dir)

    // let file_ext = args.file.extension().unwrap().to_lowercase();
    // match file_ext.as_str() {
    // "xex" => read_xex(args.file, out_dir),
    // "exe" => read_exe(args.file, out_dir),
    // _ => read_other(args.file, out_dir),
    // }
}

// fn read_xex(xex_path: Utf8NativePathBuf, out_dir: Utf8NativePathBuf) -> Result<()> {
//     Ok(())
// }

// fn read_exe(exe_path: Utf8NativePathBuf, out_dir: Utf8NativePathBuf) -> Result<()> {
//     Ok(())
// }

fn read_other(path: Utf8NativePathBuf, out_dir: Utf8NativePathBuf) -> Result<()> {
    println!("File isn't a XEX or EXE, but let's search it for PNGs anyway lol.");

    let file = File::open(path)?;
    let bytes = BufReader::new(file).bytes();
    let mut search = PngSearch::new(out_dir);

    for byte in bytes {
        search.add_byte(byte?)?;
    }

    Ok(())
}

/// Standard PNG header.
const PNG_HEADER: [u8; 8] = [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A];
/// PNGs end in 4 nulls, 'IEND', and a 4-byte CRC.
const PNG_FOOTER: [u8; 8] = [0, 0, 0, 0, 0x49, 0x45, 0x4E, 0x44];

struct PngSearch {
    file_buffer: Vec<u8>,
    png_count: u32,
    header_idx: usize,
    footer_idx: usize,
    out_dir: Utf8NativePathBuf,
}

impl PngSearch {
    pub fn new(out_dir: Utf8NativePathBuf) -> PngSearch {
        PngSearch { file_buffer: Vec::new(), png_count: 0, header_idx: 0, footer_idx: 0, out_dir }
    }

    pub fn add_byte(&mut self, byte: u8) -> Result<()> {
        match self.header_idx {
            // search for the full header
            0..=7 => {
                if PNG_HEADER[self.header_idx] == byte {
                    self.header_idx += 1;
                    self.file_buffer.push(byte);
                } else {
                    self.header_idx = 0;
                    self.file_buffer = Vec::new();
                }
            }
            // found a header
            _ => match self.footer_idx {
                // read contents / search for the footer
                0..=7 => {
                    self.file_buffer.push(byte);

                    if PNG_FOOTER[self.footer_idx] == byte {
                        self.footer_idx += 1;
                    } else {
                        self.footer_idx = 0;
                    }
                }
                // last 4 bytes are a CRC
                8..=11 => {
                    self.file_buffer.push(byte);
                    self.footer_idx += 1;
                }
                // found a footer, flush the buffer
                _ => {
                    self.png_count += 1;
                    let filename = format!("{:0>4}.png", self.png_count);
                    let dest = self.out_dir.join(filename);
                    std::fs::write(&dest, &self.file_buffer)?;
                    println!("Wrote {dest}");

                    self.file_buffer = Vec::new();
                    self.header_idx = 0;
                    self.footer_idx = 0;
                }
            },
        }
        Ok(())
    }
}
