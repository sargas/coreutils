use std::borrow::Cow;
use std::ffi::{OsStr, OsString};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Token {
    LParen,
    RParen,
    Literal(OsString),
    Negation,
    BinaryOp(BinaryOp),
    UnaryStringOp(UnaryStringOp),
    BinaryStringOp(BinaryStringOp),
    BinaryIntegerOp(BinaryIntegerOp),
    StringLength,
}

impl Token {
    pub fn as_os_string(&self) -> Cow<'static, OsStr> {
        match self {
            Token::LParen => Cow::Borrowed(OsStr::new("(")),
            Token::RParen => Cow::Borrowed(OsStr::new(")")),
            Token::Literal(s) => Cow::Owned(s.clone()),
            Token::Negation => Cow::Borrowed(OsStr::new("!")),
            Token::BinaryOp(op) => Cow::Borrowed(OsStr::new(op.as_string_value())),
            Token::UnaryStringOp(op) => Cow::Borrowed(OsStr::new(op.as_string_value())),
            Token::BinaryStringOp(op) => Cow::Borrowed(OsStr::new(op.as_string_value())),
            Token::BinaryIntegerOp(op) => Cow::Borrowed(OsStr::new(op.as_string_value())),
            Token::StringLength => Cow::Borrowed(OsStr::new("-l")),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum BinaryStringOp {
    Equals,
    NotEquals,
    SameFile, // by device and inode numbers
    NewerThan,
    OlderThan,
}

impl BinaryStringOp {
    pub fn as_string_value(&self) -> &'static str {
        match self {
            Self::Equals => "=",
            Self::NotEquals => "!=",
            BinaryStringOp::SameFile => "-ef",
            BinaryStringOp::NewerThan => "-nt",
            BinaryStringOp::OlderThan => "-ot",
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum BinaryIntegerOp {
    Equals,
    NotEquals,
    GreaterOrEqual,
    Greater,
    LessThanOrEqual,
    LessThan,
}

impl BinaryIntegerOp {
    pub fn as_string_value(&self) -> &'static str {
        match self {
            Self::Equals => "-eq",
            Self::NotEquals => "-ne",
            Self::GreaterOrEqual => "-ge",
            Self::Greater => "-gt",
            Self::LessThanOrEqual => "-le",
            Self::LessThan => "-lt",
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum BinaryOp {
    And,
    Or,
}

impl BinaryOp {
    pub fn as_string_value(&self) -> &'static str {
        match self {
            Self::And => "-a",
            Self::Or => "-o",
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum UnaryStringOp {
    NonZeroLength,
    ZeroLength,

    IsBlockSpecialFile,
    IsCharacterSpecialFile,
    IsDirectory,
    IsExistingFile,
    IsExistingRegularFile,
    IsSetGroupId,
    IsOwnedByEffectiveGroupId,
    IsSymbolicLink(IsSymbolicLink),
    IsSticky,
    ModifiedSinceRead,
    IsOwnedByEffectiveUserId,
    IsNamedPipe,
    IsReadable,
    IsNotEmpty,
    IsSocket,
}

/// Representation of the IsSymbolicLink test to use for outputting errors
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum IsSymbolicLink {
    LowerH,
    UpperL,
}

impl UnaryStringOp {
    pub fn as_string_value(&self) -> &'static str {
        match self {
            Self::NonZeroLength => "-n",
            Self::ZeroLength => "-z",
            Self::IsBlockSpecialFile => "-b",
            Self::IsCharacterSpecialFile => "-c",
            Self::IsDirectory => "-d",
            Self::IsExistingFile => "-e",
            Self::IsExistingRegularFile => "-f",
            Self::IsSetGroupId => "-g",
            Self::IsOwnedByEffectiveGroupId => "-G",
            Self::IsSymbolicLink(IsSymbolicLink::LowerH) => "-h",
            Self::IsSymbolicLink(IsSymbolicLink::UpperL) => "-L",
            Self::IsSticky => "-k",
            Self::ModifiedSinceRead => "-N",
            Self::IsOwnedByEffectiveUserId => "-O",
            Self::IsNamedPipe => "-p",
            Self::IsReadable => "-r",
            Self::IsNotEmpty => "-s",
            Self::IsSocket => "-S",
        }
    }
}

pub fn tokenize(input: Vec<OsString>) -> Vec<Token> {
    input
        .iter()
        .map(|input| match input.to_str() {
            Some("(") => Token::LParen,
            Some(")") => Token::RParen,
            Some("!") => Token::Negation,
            Some("-a") => Token::BinaryOp(BinaryOp::And),
            Some("-o") => Token::BinaryOp(BinaryOp::Or),
            Some("-n") => Token::UnaryStringOp(UnaryStringOp::NonZeroLength),
            Some("-z") => Token::UnaryStringOp(UnaryStringOp::ZeroLength),
            Some("=") => Token::BinaryStringOp(BinaryStringOp::Equals),
            Some("==") => Token::BinaryStringOp(BinaryStringOp::Equals),
            Some("!=") => Token::BinaryStringOp(BinaryStringOp::NotEquals),
            Some("-eq") => Token::BinaryIntegerOp(BinaryIntegerOp::Equals),
            Some("-ge") => Token::BinaryIntegerOp(BinaryIntegerOp::GreaterOrEqual),
            Some("-gt") => Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
            Some("-le") => Token::BinaryIntegerOp(BinaryIntegerOp::LessThanOrEqual),
            Some("-lt") => Token::BinaryIntegerOp(BinaryIntegerOp::LessThan),
            Some("-ne") => Token::BinaryIntegerOp(BinaryIntegerOp::NotEquals),
            Some("-l") => Token::StringLength,
            Some("-ef") => Token::BinaryStringOp(BinaryStringOp::SameFile),
            Some("-nt") => Token::BinaryStringOp(BinaryStringOp::NewerThan),
            Some("-ot") => Token::BinaryStringOp(BinaryStringOp::OlderThan),
            Some("-b") => Token::UnaryStringOp(UnaryStringOp::IsBlockSpecialFile),
            Some("-c") => Token::UnaryStringOp(UnaryStringOp::IsCharacterSpecialFile),
            Some("-d") => Token::UnaryStringOp(UnaryStringOp::IsDirectory),
            Some("-e") => Token::UnaryStringOp(UnaryStringOp::IsExistingFile),
            Some("-f") => Token::UnaryStringOp(UnaryStringOp::IsExistingRegularFile),
            Some("-g") => Token::UnaryStringOp(UnaryStringOp::IsSetGroupId),
            Some("-G") => Token::UnaryStringOp(UnaryStringOp::IsOwnedByEffectiveGroupId),
            Some("-h") => {
                Token::UnaryStringOp(UnaryStringOp::IsSymbolicLink(IsSymbolicLink::LowerH))
            }
            Some("-k") => Token::UnaryStringOp(UnaryStringOp::IsSticky),
            Some("-L") => {
                Token::UnaryStringOp(UnaryStringOp::IsSymbolicLink(IsSymbolicLink::UpperL))
            }
            Some("-N") => Token::UnaryStringOp(UnaryStringOp::ModifiedSinceRead),
            Some("-O") => Token::UnaryStringOp(UnaryStringOp::IsOwnedByEffectiveUserId),
            Some("-p") => Token::UnaryStringOp(UnaryStringOp::IsNamedPipe),
            Some("-r") => Token::UnaryStringOp(UnaryStringOp::IsReadable),
            Some("-s") => Token::UnaryStringOp(UnaryStringOp::IsNotEmpty),
            Some("-S") => Token::UnaryStringOp(UnaryStringOp::IsSocket),

            _ => Token::Literal(input.clone()),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::lexer::{
        tokenize, BinaryIntegerOp, BinaryOp, BinaryStringOp, IsSymbolicLink, Token, UnaryStringOp,
    };
    use rstest::rstest;
    use std::borrow::Cow;

    #[test]
    fn simple_tokenizing() {
        assert_eq!(
            tokenize(vec!["true".into()]),
            vec![Token::Literal("true".into())],
        );

        assert_eq!(
            tokenize(vec!["(".into(), "true".into(), ")".into()]),
            vec![Token::LParen, Token::Literal("true".into()), Token::RParen],
        );

        assert_eq!(
            tokenize(vec!["!".into(), "true".into()]),
            vec![Token::Negation, Token::Literal("true".into())],
        );

        assert_eq!(
            tokenize(vec!["a".into(), "-a".into(), "b".into()]),
            vec![
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::Literal("b".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["a".into(), "-o".into(), "b".into()]),
            vec![
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::Or),
                Token::Literal("b".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["-n".into(), "true".into()]),
            vec![
                Token::UnaryStringOp(UnaryStringOp::NonZeroLength),
                Token::Literal("true".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["-z".into(), "true".into()]),
            vec![
                Token::UnaryStringOp(UnaryStringOp::ZeroLength),
                Token::Literal("true".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["true".into(), "=".into(), "false".into()]),
            vec![
                Token::Literal("true".into()),
                Token::BinaryStringOp(BinaryStringOp::Equals),
                Token::Literal("false".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["true".into(), "==".into(), "false".into()]),
            vec![
                Token::Literal("true".into()),
                Token::BinaryStringOp(BinaryStringOp::Equals),
                Token::Literal("false".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["true".into(), "!=".into(), "false".into()]),
            vec![
                Token::Literal("true".into()),
                Token::BinaryStringOp(BinaryStringOp::NotEquals),
                Token::Literal("false".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["1".into(), "-eq".into(), "2".into()]),
            vec![
                Token::Literal("1".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Equals),
                Token::Literal("2".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["1".into(), "-ge".into(), "2".into()]),
            vec![
                Token::Literal("1".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::GreaterOrEqual),
                Token::Literal("2".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["1".into(), "-gt".into(), "2".into()]),
            vec![
                Token::Literal("1".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
                Token::Literal("2".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["1".into(), "-le".into(), "2".into()]),
            vec![
                Token::Literal("1".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::LessThanOrEqual),
                Token::Literal("2".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["1".into(), "-lt".into(), "2".into()]),
            vec![
                Token::Literal("1".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::LessThan),
                Token::Literal("2".into())
            ],
        );

        assert_eq!(
            tokenize(vec!["1".into(), "-ne".into(), "2".into()]),
            vec![
                Token::Literal("1".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::NotEquals),
                Token::Literal("2".into())
            ],
        );

        assert_eq!(
            tokenize(vec![
                "-ef".into(),
                "-nt".into(),
                "-ot".into(),
                "-b".into(),
                "-c".into(),
                "-d".into(),
                "-e".into(),
                "-f".into(),
                "-g".into(),
                "-G".into(),
                "-h".into(),
                "-k".into(),
                "-L".into(),
                "-N".into(),
                "-O".into(),
                "-p".into(),
                "-r".into(),
                "-s".into(),
                "-S".into(),
                // "-t".into(), "-u".into(),"-w".into(), "-x".into(),
            ]),
            vec![
                Token::BinaryStringOp(BinaryStringOp::SameFile),
                Token::BinaryStringOp(BinaryStringOp::NewerThan),
                Token::BinaryStringOp(BinaryStringOp::OlderThan),
                Token::UnaryStringOp(UnaryStringOp::IsBlockSpecialFile),
                Token::UnaryStringOp(UnaryStringOp::IsCharacterSpecialFile),
                Token::UnaryStringOp(UnaryStringOp::IsDirectory),
                Token::UnaryStringOp(UnaryStringOp::IsExistingFile),
                Token::UnaryStringOp(UnaryStringOp::IsExistingRegularFile),
                Token::UnaryStringOp(UnaryStringOp::IsSetGroupId),
                Token::UnaryStringOp(UnaryStringOp::IsOwnedByEffectiveGroupId),
                Token::UnaryStringOp(UnaryStringOp::IsSymbolicLink(IsSymbolicLink::LowerH)),
                Token::UnaryStringOp(UnaryStringOp::IsSticky),
                Token::UnaryStringOp(UnaryStringOp::IsSymbolicLink(IsSymbolicLink::UpperL)),
                Token::UnaryStringOp(UnaryStringOp::ModifiedSinceRead),
                Token::UnaryStringOp(UnaryStringOp::IsOwnedByEffectiveUserId),
                Token::UnaryStringOp(UnaryStringOp::IsNamedPipe),
                Token::UnaryStringOp(UnaryStringOp::IsReadable),
                Token::UnaryStringOp(UnaryStringOp::IsNotEmpty),
                Token::UnaryStringOp(UnaryStringOp::IsSocket),
            ],
        );

        assert_eq!(
            tokenize(vec!["-l".into(), "electroencephalograph".into()]),
            vec![
                Token::StringLength,
                Token::Literal("electroencephalograph".into())
            ],
        );
    }

    #[rstest]
    #[case::literal(Token::Literal("hello".into()), "hello")]
    #[case::lparen(Token::LParen, "(")]
    #[case::right(Token::RParen, ")")]
    #[case::negation(Token::Negation, "!")]
    #[case::and(Token::BinaryOp(BinaryOp::And), "-a")]
    #[case::or(Token::BinaryOp(BinaryOp::Or), "-o")]
    #[case::nonzero_length(Token::UnaryStringOp(UnaryStringOp::NonZeroLength), "-n")]
    #[case::zero_length(Token::UnaryStringOp(UnaryStringOp::ZeroLength), "-z")]
    #[case::string_equals(Token::BinaryStringOp(BinaryStringOp::Equals), "=")]
    #[case::string_not_equals(Token::BinaryStringOp(BinaryStringOp::NotEquals), "!=")]
    #[case::integer_equals(Token::BinaryIntegerOp(BinaryIntegerOp::Equals), "-eq")]
    #[case::integer_not_equals(Token::BinaryIntegerOp(BinaryIntegerOp::NotEquals), "-ne")]
    #[case::integer_greater(Token::BinaryIntegerOp(BinaryIntegerOp::Greater), "-gt")]
    #[case::integer_greater_or_equal(
        Token::BinaryIntegerOp(BinaryIntegerOp::GreaterOrEqual),
        "-ge"
    )]
    #[case::integer_less_than(Token::BinaryIntegerOp(BinaryIntegerOp::LessThan), "-lt")]
    #[case::integer_less_than_or_equal(
        Token::BinaryIntegerOp(BinaryIntegerOp::LessThanOrEqual),
        "-le"
    )]
    #[case::files_same(Token::BinaryStringOp(BinaryStringOp::SameFile), "-ef")]
    #[case::files_newer(Token::BinaryStringOp(BinaryStringOp::NewerThan), "-nt")]
    #[case::files_older(Token::BinaryStringOp(BinaryStringOp::OlderThan), "-ot")]
    #[case::string_length(Token::StringLength, "-l")]
    fn as_string_value(#[case] token: Token, #[case] expected: &str) {
        assert_eq!(token.as_os_string(), Cow::Borrowed(expected.into()),);
    }
}
