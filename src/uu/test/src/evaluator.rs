use std::ffi::OsStr;
use std::fs;
use std::fs::Metadata;
use std::ops::Not;
#[cfg(unix)]
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::path::Path;
use std::time::SystemTime;

use uucore::error::UResult;
#[cfg(not(unix))]
use uucore::error::USimpleError;
use uucore::fs::FileInformation;
#[cfg(unix)]
use uucore::process::{getegid, geteuid};

use crate::lexer::{BinaryIntegerOp, BinaryOp, BinaryStringOp, UnaryStringOp};
use crate::parserv2::{BooleanExpr, IntegerExpr};

const S_ISGID: u32 = 0o2000;
const S_ISVTX: u32 = 0o1000;

pub fn eval(expr: &BooleanExpr) -> UResult<bool> {
    match expr {
        BooleanExpr::Negation(e) => eval(e).map(Not::not),

        BooleanExpr::BinaryOp {
            left,
            op: BinaryOp::And,
            right,
        } => Ok(eval(left)? && eval(right)?),
        BooleanExpr::BinaryOp {
            left,
            op: BinaryOp::Or,
            right,
        } => Ok(eval(left)? || eval(right)?),

        BooleanExpr::UnaryStringOp(UnaryStringOp::NonZeroLength, s) => Ok(!s.is_empty()),
        BooleanExpr::UnaryStringOp(UnaryStringOp::ZeroLength, s) => Ok(s.is_empty()),

        BooleanExpr::UnaryStringOp(UnaryStringOp::IsBlockSpecialFile, file) => {
            is_block_device(&file)
        }
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsCharacterSpecialFile, file) => {
            Ok(is_character_device(&file))
        }
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsDirectory, file) => Ok(fs::metadata(file)
            .map(|m| m.file_type().is_dir())
            .unwrap_or(false)),
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsExistingFile, file) => {
            Ok(fs::metadata(file).is_ok())
        }
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsExistingRegularFile, file) => {
            Ok(fs::metadata(file)
                .map(|m| m.file_type().is_file())
                .unwrap_or(false))
        }
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsSetGroupId, file) => {
            Ok(has_unix_bit_set(file, S_ISGID))
        }
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsOwnedByEffectiveGroupId, file) => {
            Ok(is_owned_by_effective_gid(file))
        }
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsSymbolicLink(_), file) => {
            Ok(fs::symlink_metadata(file)
                .map(|m| m.is_symlink())
                .unwrap_or(false))
        }
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsSticky, file) => {
            Ok(has_unix_bit_set(file, S_ISVTX))
        }
        BooleanExpr::UnaryStringOp(UnaryStringOp::ModifiedSinceRead, file) => Ok({
            let metadata = fs::metadata(file)?;
            metadata
                .modified()
                .and_then(|m| metadata.accessed().map(|a| m > a))
                .unwrap_or(false)
        }),
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsOwnedByEffectiveUserId, file) => {
            Ok(is_owned_by_effective_uid(file))
        }
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsNamedPipe, file) => Ok(fs::metadata(file)
            .map(|m| m.file_type().is_fifo())
            .unwrap_or(false)),
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsReadable, file) => Ok(fs::metadata(file)
            .map(|m| check_permission(m, 0o4))
            .unwrap_or(false)),
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsNotEmpty, file) => {
            Ok(fs::metadata(file).map(|m| m.len() > 0).unwrap_or(false))
        }
        BooleanExpr::UnaryStringOp(UnaryStringOp::IsSocket, file) => is_socket(file),

        BooleanExpr::BinaryStringOp {
            left,
            op: BinaryStringOp::Equals,
            right,
        } => Ok(left == right),
        BooleanExpr::BinaryStringOp {
            left,
            op: BinaryStringOp::NotEquals,
            right,
        } => Ok(left != right),

        BooleanExpr::BinaryIntegerOp {
            left,
            op: BinaryIntegerOp::Equals,
            right,
        } => Ok(eval_int(left) == eval_int(right)),
        BooleanExpr::BinaryIntegerOp {
            left,
            op: BinaryIntegerOp::NotEquals,
            right,
        } => Ok(eval_int(left) != eval_int(right)),
        BooleanExpr::BinaryIntegerOp {
            left,
            op: BinaryIntegerOp::GreaterOrEqual,
            right,
        } => Ok(eval_int(left) >= eval_int(right)),
        BooleanExpr::BinaryIntegerOp {
            left,
            op: BinaryIntegerOp::Greater,
            right,
        } => Ok(eval_int(left) > eval_int(right)),
        BooleanExpr::BinaryIntegerOp {
            left,
            op: BinaryIntegerOp::LessThanOrEqual,
            right,
        } => Ok(eval_int(left) <= eval_int(right)),
        BooleanExpr::BinaryIntegerOp {
            left,
            op: BinaryIntegerOp::LessThan,
            right,
        } => Ok(eval_int(left) < eval_int(right)),

        BooleanExpr::EmptyExpression => Ok(false),
        BooleanExpr::BinaryStringOp {
            left,
            op: BinaryStringOp::SameFile,
            right,
        } => {
            let left_info = match FileInformation::from_path(left, true) {
                Ok(info) => info,
                Err(_) => return Ok(false),
            };
            let right_info = match FileInformation::from_path(right, true) {
                Ok(info) => info,
                Err(_) => return Ok(false),
            };

            Ok(left_info == right_info)
        }
        BooleanExpr::BinaryStringOp {
            left,
            op: BinaryStringOp::NewerThan,
            right,
        } => compare_modification_times(left, SystemTime::gt, right),
        BooleanExpr::BinaryStringOp {
            left,
            op: BinaryStringOp::OlderThan,
            right,
        } => compare_modification_times(left, SystemTime::lt, right),
    }
}

#[cfg(unix)]
fn check_permission(metadata: Metadata, p: u32) -> bool {
    if geteuid() == metadata.uid() {
        metadata.mode() & (p << 6) != 0
    } else if getegid() == metadata.gid() {
        metadata.mode() & (p << 3) != 0
    } else {
        metadata.mode() & p != 0
    }
}
#[cfg(not(unix))]
fn check_permission(_metadata: Metadata, _p: u32) -> bool {
    false
}

#[cfg(unix)]
fn is_owned_by_effective_gid(file: impl AsRef<Path>) -> bool {
    fs::metadata(file)
        .map(|m| m.gid() == getegid())
        .unwrap_or(false)
}
#[cfg(not(unix))]
fn is_owned_by_effective_gid(_: impl AsRef<Path>) -> bool {
    false
}

#[cfg(unix)]
fn has_unix_bit_set(file: impl AsRef<Path>, bit: u32) -> bool {
    fs::metadata(file)
        .map(|m| m.mode() & bit != 0)
        .unwrap_or(false)
}

#[cfg(not(unix))]
fn has_unix_bit_set(_file: impl AsRef<Path>, _bit: u32) -> bool {
    false
}

#[cfg(unix)]
fn is_block_device(file: impl AsRef<Path>) -> UResult<bool> {
    Ok(fs::metadata(file)
        .map(|m| m.file_type().is_block_device())
        .unwrap_or(false))
}

#[cfg(not(unix))]
fn is_block_device(_: impl AsRef<Path>) -> UResult<bool> {
    only_unix_error()
}

#[cfg(not(unix))]
fn only_unix_error<T>() -> UResult<T> {
    Err(USimpleError::new(2, "Unsupported on Windows"))
}

#[cfg(unix)]
fn is_character_device(file: impl AsRef<Path>) -> bool {
    fs::metadata(file)
        .map(|m| m.file_type().is_char_device())
        .unwrap_or(false)
}

#[cfg(not(unix))]
fn is_character_device(_: impl AsRef<Path>) -> bool {
    false
}

#[cfg(unix)]
fn is_socket(file: impl AsRef<Path>) -> UResult<bool> {
    Ok(fs::metadata(file)
        .map(|m| m.file_type().is_socket())
        .unwrap_or(false))
}

#[cfg(not(unix))]
fn is_socket(_: impl AsRef<Path>) -> UResult<bool> {
    // Unlike other types of tests, Windows _does_ have a concept of sockets
    // (unix domain sockets) with a proposal to add them to the Rust standard
    // library at https://github.com/rust-lang/libs-team/issues/271
    Err(USimpleError::new(
        2,
        "-S currently only supported on *nix platforms",
    ))
}

fn compare_modification_times(
    left: &OsStr,
    op: impl Fn(&SystemTime, &SystemTime) -> bool,
    right: &OsStr,
) -> UResult<bool> {
    let left = match fs::metadata(left).and_then(|m| m.modified()) {
        Ok(t) => t,
        Err(_) => return Ok(false),
    };
    let right = match fs::metadata(right).and_then(|m| m.modified()) {
        Ok(t) => t,
        Err(_) => return Ok(false),
    };

    Ok(op(&left, &right))
}

#[cfg(unix)]
fn is_owned_by_effective_uid(file: impl AsRef<Path>) -> bool {
    fs::metadata(file)
        .map(|m| m.uid() == geteuid())
        .unwrap_or(false)
}
#[cfg(not(unix))]
fn is_owned_by_effective_uid(_: impl AsRef<Path>) -> bool {
    false
}

fn eval_int(value: &IntegerExpr) -> i64 {
    match value {
        IntegerExpr::Integer(i) => *i,
        IntegerExpr::Length(s) => s.len() as i64,
    }
}

#[cfg(test)]
mod tests {
    #[cfg(unix)]
    use std::ffi::CString;
    use std::fs;
    #[cfg(unix)]
    use std::fs::Permissions;
    use std::fs::{File, FileTimes};
    use std::io::Write;
    #[cfg(unix)]
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    #[cfg(unix)]
    use std::os::unix::net::UnixListener;
    use std::path::Path;
    use std::time::{Duration, SystemTime};

    #[cfg(unix)]
    use libc::mkfifo;
    use rstest::rstest;
    use tempfile::NamedTempFile;

    use uucore::error::UResult;
    #[cfg(unix)]
    use uucore::error::USimpleError;
    #[cfg(unix)]
    use uucore::perms;
    #[cfg(unix)]
    use uucore::process::{getegid, geteuid};

    use crate::evaluator::{eval, eval_int};
    #[cfg(unix)]
    use crate::evaluator::{S_ISGID, S_ISVTX};
    use crate::lexer::{BinaryIntegerOp, BinaryOp, BinaryStringOp, IsSymbolicLink, UnaryStringOp};
    use crate::parserv2::{BooleanExpr, IntegerExpr, StringExpr};

    #[rstest]
    #[case::empty(BooleanExpr::EmptyExpression, false)]
    #[case::empty_literal(BooleanExpr::UnaryStringOp(UnaryStringOp::NonZeroLength, "".into()), false)]
    #[case::literal(BooleanExpr::UnaryStringOp(UnaryStringOp::NonZeroLength, "hello".into()), true)]
    #[case::zero_length_empty_string(BooleanExpr::UnaryStringOp(UnaryStringOp::ZeroLength, "".into()), true)]
    #[case::zero_length_nonempty_string(BooleanExpr::UnaryStringOp(UnaryStringOp::ZeroLength, "hello".into()), false)]
    #[case::strings_equal_true(BooleanExpr::BinaryStringOp{op: BinaryStringOp::Equals, left: "a".into(), right: "a".into()}, true)]
    #[case::strings_equal_false(BooleanExpr::BinaryStringOp{op: BinaryStringOp::Equals, left: "a".into(), right: "b".into()}, false)]
    #[case::negate_expression(BooleanExpr::Negation(Box::new(BooleanExpr::UnaryStringOp(UnaryStringOp::NonZeroLength, "".into()))), true)]
    #[case::ints_equal(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::Equals, right: IntegerExpr::Integer(3)}, true)]
    #[case::ints_equal(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::Equals, right: IntegerExpr::Integer(8)}, false)]
    #[case::ints_not_equal(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::NotEquals, right: IntegerExpr::Integer(3)}, false)]
    #[case::ints_not_equal(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::NotEquals, right: IntegerExpr::Integer(2)}, true)]
    #[case::greater_or_equal(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::GreaterOrEqual, right: IntegerExpr::Integer(2)}, true)]
    #[case::greater_or_equal(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::GreaterOrEqual, right: IntegerExpr::Integer(3)}, true)]
    #[case::greater_or_equal(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::GreaterOrEqual, right: IntegerExpr::Integer(4)}, false)]
    #[case::greater(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::Greater, right: IntegerExpr::Integer(2)}, true)]
    #[case::greater(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::Greater, right: IntegerExpr::Integer(3)}, false)]
    #[case::greater(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::Greater, right: IntegerExpr::Integer(4)}, false)]
    #[case::lesser_or_equal(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::LessThanOrEqual, right: IntegerExpr::Integer(2)}, false)]
    #[case::lesser_or_equal(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::LessThanOrEqual, right: IntegerExpr::Integer(3)}, true)]
    #[case::lesser_or_equal(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::LessThanOrEqual, right: IntegerExpr::Integer(4)}, true)]
    #[case::lesser(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::LessThan, right: IntegerExpr::Integer(2)}, false)]
    #[case::lesser(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::LessThan, right: IntegerExpr::Integer(3)}, false)]
    #[case::lesser(BooleanExpr::BinaryIntegerOp {left: IntegerExpr::Integer(3), op: BinaryIntegerOp::LessThan, right: IntegerExpr::Integer(4)}, true)]
    fn evaluate_simple_expression(#[case] input: BooleanExpr, #[case] output: bool) {
        assert_eq!(eval(&input).unwrap(), output);
    }

    // Whether these expressions actually evaluate to true or false is confirmed by the unit test above
    // These two are functions instead of constants because the boolean expressions take ownership of the OsStr's
    fn true_expr() -> BooleanExpr {
        BooleanExpr::UnaryStringOp(UnaryStringOp::NonZeroLength, "hello".into())
    }
    fn false_expr() -> BooleanExpr {
        BooleanExpr::UnaryStringOp(UnaryStringOp::NonZeroLength, "".into())
    }

    #[rstest]
    #[case(true_expr(), BinaryOp::And, true_expr(), true)]
    #[case(true_expr(), BinaryOp::And, false_expr(), false)]
    #[case(false_expr(), BinaryOp::And, true_expr(), false)]
    #[case(false_expr(), BinaryOp::And, false_expr(), false)]
    #[case(true_expr(), BinaryOp::Or, true_expr(), true)]
    #[case(true_expr(), BinaryOp::Or, false_expr(), true)]
    #[case(false_expr(), BinaryOp::Or, true_expr(), true)]
    #[case(false_expr(), BinaryOp::Or, false_expr(), false)]
    fn boolean_logic_combinations(
        #[case] left: BooleanExpr,
        #[case] op: BinaryOp,
        #[case] right: BooleanExpr,
        #[case] expected: bool,
    ) {
        assert_eq!(
            eval(&BooleanExpr::BinaryOp {
                left: Box::new(left),
                op,
                right: Box::new(right)
            })
            .unwrap(),
            expected
        );
    }

    #[test]
    fn string_length() {
        assert_eq!(eval_int(&IntegerExpr::Length("".into())), 0,);
        assert_eq!(eval_int(&IntegerExpr::Length("a".into())), 1,);
        assert_eq!(eval_int(&IntegerExpr::Length("1234567890".into())), 10,);
    }

    #[test]
    fn file_equality() -> UResult<()> {
        let temp_dir = tempfile::tempdir()?;

        let file1 = temp_dir.path().join("file1").into_os_string();
        drop(File::create(&file1)?);

        let file2 = temp_dir.path().join("file2").into_os_string();
        fs::hard_link(&file1, &file2)?;

        let file3 = temp_dir.path().join("file3").into_os_string();
        drop(File::create(&file3)?);

        let file4 = temp_dir.path().join("file4").into_os_string();
        #[cfg(unix)]
        std::os::unix::fs::symlink(&file2, &file4)?;
        #[cfg(windows)]
        std::os::windows::fs::symlink_file(&file2, &file4)?;

        assert!(eval(&BooleanExpr::BinaryStringOp {
            left: file1.clone(),
            op: BinaryStringOp::SameFile,
            right: file2.clone(),
        })?);

        assert!(!eval(&BooleanExpr::BinaryStringOp {
            left: file1.clone(),
            op: BinaryStringOp::SameFile,
            right: file3.clone(),
        })?);

        assert!(eval(&BooleanExpr::BinaryStringOp {
            left: file1.clone(),
            op: BinaryStringOp::SameFile,
            right: file4.clone(),
        })?);

        Ok(())
    }

    #[test]
    fn file_timestamp_comparison() -> UResult<()> {
        let temp_dir = tempfile::tempdir()?;
        let now = SystemTime::now();

        let earliest = temp_dir.path().join("file1").into_os_string();
        create_file_with_modification_time(&earliest, now - Duration::from_secs(100))?;

        let newest = temp_dir.path().join("file2").into_os_string();
        create_file_with_modification_time(&newest, now - Duration::from_secs(10))?;

        assert!(!eval(&BooleanExpr::BinaryStringOp {
            left: earliest.clone(),
            op: BinaryStringOp::NewerThan,
            right: newest.clone(),
        })?);
        assert!(eval(&BooleanExpr::BinaryStringOp {
            left: earliest.clone(),
            op: BinaryStringOp::OlderThan,
            right: newest.clone(),
        })?);
        assert!(eval(&BooleanExpr::BinaryStringOp {
            left: newest.clone(),
            op: BinaryStringOp::NewerThan,
            right: earliest.clone(),
        })?);
        assert!(!eval(&BooleanExpr::BinaryStringOp {
            left: newest.clone(),
            op: BinaryStringOp::OlderThan,
            right: earliest.clone(),
        })?);

        Ok(())
    }

    struct FileTypeTestArgs {
        is_block: bool,
        is_char: bool,
        is_directory: bool,
        exists: bool,
        is_regular_file: bool,
    }
    fn run_file_type_tests(file: StringExpr, args: FileTypeTestArgs) -> UResult<()> {
        #[cfg(unix)]
        assert_eq!(
            eval(&BooleanExpr::UnaryStringOp(
                UnaryStringOp::IsBlockSpecialFile,
                file.clone()
            ))?,
            args.is_block
        );
        #[cfg(unix)]
        assert_eq!(
            eval(&BooleanExpr::UnaryStringOp(
                UnaryStringOp::IsCharacterSpecialFile,
                file.clone()
            ))?,
            args.is_char
        );
        assert_eq!(
            eval(&BooleanExpr::UnaryStringOp(
                UnaryStringOp::IsDirectory,
                file.clone()
            ))?,
            args.is_directory
        );
        assert_eq!(
            eval(&BooleanExpr::UnaryStringOp(
                UnaryStringOp::IsExistingFile,
                file.clone()
            ))?,
            args.exists
        );
        assert_eq!(
            eval(&BooleanExpr::UnaryStringOp(
                UnaryStringOp::IsExistingRegularFile,
                file.clone()
            ))?,
            args.is_regular_file
        );

        Ok(())
    }

    #[test]
    fn file_type_tests() -> UResult<()> {
        let directory = tempfile::tempdir()?;
        let regular_file = NamedTempFile::new()?;
        let nonexistent_file = directory.path().join("non-existent");

        #[cfg(unix)]
        run_file_type_tests(
            "/dev/zero".into(),
            FileTypeTestArgs {
                is_block: false,
                is_char: true,
                is_directory: false,
                exists: true,
                is_regular_file: false,
            },
        )?;
        run_file_type_tests(
            directory.path().into(),
            FileTypeTestArgs {
                is_block: false,
                is_char: false,
                is_directory: true,
                exists: true,
                is_regular_file: false,
            },
        )?;
        run_file_type_tests(
            regular_file.path().into(),
            FileTypeTestArgs {
                is_block: false,
                is_char: false,
                is_directory: false,
                exists: true,
                is_regular_file: true,
            },
        )?;
        run_file_type_tests(
            nonexistent_file.into_os_string(),
            FileTypeTestArgs {
                is_block: false,
                is_char: false,
                is_directory: false,
                exists: false,
                is_regular_file: false,
            },
        )?;

        Ok(())
    }

    #[test]
    #[cfg(unix)]
    fn file_type_block_device() -> UResult<()> {
        // More examples in https://www.kernel.org/doc/html/latest/admin-guide/devices.html
        let block_file = [
            "/dev/root",
            "/dev/sda",
            "/dev/hda",
            "/dev/loop0",
            "/dev/md0",
            "/dev/sr0",
            "/dev/sg0",
            "/dev/mmcblk0",
            "/dev/nvme0n1",
            "/dev/dm-0",
        ]
        .iter()
        .find(|f| fs::metadata(f).is_ok());
        if let Some(block_file) = block_file {
            assert!(
                eval(&BooleanExpr::UnaryStringOp(
                    UnaryStringOp::IsBlockSpecialFile,
                    block_file.into()
                ))?,
                "{block_file} is not testing as a block device"
            );
        } else {
            eprintln!("Unable to test block devices - none found");
        }
        Ok(())
    }

    #[cfg(windows)]
    #[test]
    fn file_type_windows_tests() {
        let file = NamedTempFile::new()?;

        assert!(eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsBlockSpecialFile,
            file.path().into()
        ))
        .is_err());
        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsCharacterSpecialFile,
            file.path().into()
        ))?);
    }

    #[cfg(unix)]
    #[test]
    fn test_set_gid_bit() -> UResult<()> {
        let file1 = NamedTempFile::new()?;

        let m = fs::metadata(&file1)?.mode() | S_ISGID;
        fs::set_permissions(&file1, Permissions::from_mode(m))?;

        let file2 = NamedTempFile::new()?;

        assert!(eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsSetGroupId,
            file1.path().into()
        ))?);
        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsSetGroupId,
            file2.path().into()
        ))?);

        Ok(())
    }

    #[cfg(not(unix))]
    #[test]
    fn test_set_gid_bit() -> UResult<()> {
        let file1 = NamedTempFile::new()?;
        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsSetGroupId,
            file1.path().into()
        ))?);

        Ok(())
    }

    #[cfg(unix)]
    #[ignore = "Cannot set gid of file without being root or CAP_CHOWN"]
    #[test]
    fn test_effective_gid_ownership() -> UResult<()> {
        let temp_dir = tempfile::tempdir()?;

        let file1_path = temp_dir.path().join("file1").into_os_string();
        let file1 = File::create(&file1_path)?;
        let metadata = file1.metadata()?;

        perms::wrap_chown(
            &file1_path,
            &metadata,
            None,
            Some(getegid() + 42),
            true,
            perms::Verbosity {
                groups_only: false,
                level: perms::VerbosityLevel::Verbose,
            },
        )
        .map_err(|e| USimpleError::new(0, e))?;
        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsOwnedByEffectiveGroupId,
            file1_path.clone()
        ))?);

        Ok(())
    }

    fn create_file_with_modification_time(name: impl AsRef<Path>, time: SystemTime) -> UResult<()> {
        let file = File::create(name)?;
        file.set_modified(time)?;
        drop(file);
        Ok(())
    }

    #[test]
    fn is_symbolic_link() -> UResult<()> {
        let temp_dir = tempfile::tempdir()?;

        let file1 = temp_dir.path().join("file1").into_os_string();
        drop(File::create(&file1)?);

        let file2 = temp_dir.path().join("file2").into_os_string();
        #[cfg(unix)]
        std::os::unix::fs::symlink(&file1, &file2)?;
        #[cfg(windows)]
        std::os::windows::fs::symlink_file(&file1, &file2)?;

        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsSymbolicLink(IsSymbolicLink::LowerH),
            file1.clone()
        ))?);
        assert!(eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsSymbolicLink(IsSymbolicLink::UpperL),
            file2.clone()
        ))?);

        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_has_sticky_bit() -> UResult<()> {
        let file1 = NamedTempFile::new()?;

        let m = fs::metadata(&file1)?.mode() | S_ISVTX;
        fs::set_permissions(&file1, Permissions::from_mode(m))?;

        let file2 = NamedTempFile::new()?;

        assert!(eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsSticky,
            file1.path().into()
        ))?);
        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsSticky,
            file2.path().into()
        ))?);

        Ok(())
    }

    #[cfg(not(unix))]
    #[test]
    fn test_has_sticky_bit() -> UResult<()> {
        let file1 = NamedTempFile::new()?;
        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsSticky,
            file1.path().into()
        ))?);

        Ok(())
    }

    #[test]
    fn test_modified_since_read() -> UResult<()> {
        let temp_dir = tempfile::tempdir()?;
        let now = SystemTime::now();
        let file1_path = temp_dir.path().join("file1").into_os_string();
        {
            let file = File::create(&file1_path)?;
            file.set_times(
                FileTimes::new()
                    .set_modified(now)
                    .set_accessed(now - Duration::from_secs(100)),
            )?;
        }

        let file2_path = temp_dir.path().join("file2").into_os_string();
        {
            let file = File::create(&file2_path)?;
            file.set_times(
                FileTimes::new()
                    .set_modified(now - Duration::from_secs(100))
                    .set_accessed(now),
            )?;
        }

        assert!(eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::ModifiedSinceRead,
            file1_path
        ))?);
        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::ModifiedSinceRead,
            file2_path
        ))?);

        Ok(())
    }

    #[cfg(unix)]
    #[ignore = "Cannot set uid of file without being root or CAP_CHOWN"]
    #[test]
    fn test_effective_uid_ownership() -> UResult<()> {
        let temp_dir = tempfile::tempdir()?;

        let file1_path = temp_dir.path().join("file1").into_os_string();
        let file1 = File::create(&file1_path)?;
        let metadata = file1.metadata()?;

        perms::wrap_chown(
            &file1_path,
            &metadata,
            Some(geteuid() + 42),
            None,
            true,
            perms::Verbosity {
                groups_only: false,
                level: perms::VerbosityLevel::Verbose,
            },
        )
        .map_err(|e| USimpleError::new(0, e))?;
        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsOwnedByEffectiveUserId,
            file1_path.clone()
        ))?);

        Ok(())
    }

    #[test]
    #[cfg(unix)] // Windows has a slightly different concept of a named pipe, and OSString->CString conversion is non-trivial
    fn test_named_pipe() -> UResult<()> {
        use std::os::unix::ffi::OsStrExt;
        let temp_dir = tempfile::tempdir()?;

        let file1_path = temp_dir.path().join("file1").into_os_string();
        let file1_path_cstr = CString::new(file1_path.as_bytes()).unwrap();
        let err = unsafe { mkfifo(file1_path_cstr.as_ptr(), 0e666 as libc::mode_t) };
        if err != 0 {
            panic!("Unexpected err {err}")
        }

        let file2_path = temp_dir.path().join("file2").into_os_string();
        drop(File::create(&file2_path)?);

        assert!(eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsNamedPipe,
            file1_path
        ))?);
        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsNamedPipe,
            file2_path
        ))?);

        Ok(())
    }

    #[test]
    #[cfg(unix)] // Making a file readable is only trivial on *nix: https://stackoverflow.com/a/77931167
    fn read_access() -> UResult<()> {
        use std::os::unix::fs::PermissionsExt;
        let temp_dir = tempfile::tempdir()?;

        let file1 = temp_dir.path().join("file1").into_os_string();
        drop({
            let file = File::create(&file1)?;
            let mut permissions = file.metadata()?.permissions();
            permissions.set_mode(permissions.mode() ^ 0o444);
            file.set_permissions(permissions)?;
            file
        });
        let file2 = temp_dir.path().join("file2").into_os_string();
        drop(File::create(&file2)?);

        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsReadable,
            file1
        ))?);
        assert!(eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsReadable,
            file2
        ))?);

        Ok(())
    }

    #[test]
    fn not_empty() -> UResult<()> {
        let empty_file = NamedTempFile::new()?;
        let not_empty_file = {
            let mut f = NamedTempFile::new()?;
            f.write_all(b"Test")?;
            f
        };

        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsNotEmpty,
            empty_file.path().into()
        ))?);
        assert!(eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsNotEmpty,
            not_empty_file.path().into()
        ))?);

        Ok(())
    }

    #[test]
    #[cfg(unix)]
    fn is_socket() -> UResult<()> {
        let temp_dir = tempfile::tempdir()?;
        let socket_file_path = temp_dir.path().join("socket");
        let socket_file = UnixListener::bind(&socket_file_path)?;
        let plain_file = NamedTempFile::new()?;

        assert!(!eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsSocket,
            plain_file.path().into()
        ))?);
        assert!(eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsSocket,
            socket_file_path.into_os_string()
        ))?);

        Ok(())
    }

    #[test]
    #[cfg(not(unix))]
    fn is_socket() -> UResult<()> {
        let err = eval(&BooleanExpr::UnaryStringOp(
            UnaryStringOp::IsSocket,
            "".into(),
        ))
        .err()?;
        assert_eq!(2, err.code());
        assert_eq!(false, err.usage());

        Ok(())
    }
}
