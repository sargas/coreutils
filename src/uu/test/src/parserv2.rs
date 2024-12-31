use std::ffi::OsString;
use std::iter::Peekable;

use uucore::display::Quotable;

use crate::error::{ParseError, ParseResult};
use crate::lexer::{BinaryIntegerOp, BinaryOp, BinaryStringOp, Token, UnaryStringOp};

pub type StringExpr = OsString;

#[derive(Debug, Eq, PartialEq)]
pub enum BooleanExpr {
    Negation(Box<BooleanExpr>),
    BinaryOp {
        left: Box<BooleanExpr>,
        op: BinaryOp,
        right: Box<BooleanExpr>,
    },
    UnaryStringOp(UnaryStringOp, StringExpr),
    BinaryStringOp {
        left: StringExpr,
        op: BinaryStringOp,
        right: StringExpr,
    },
    BinaryIntegerOp {
        left: IntegerExpr,
        op: BinaryIntegerOp,
        right: IntegerExpr,
    },
    EmptyExpression,
}

#[derive(Debug, Eq, PartialEq)]
pub enum IntegerExpr {
    Integer(i64), // TODO: i128?
    Length(OsString),
}

pub struct Parser<'a> {
    tokens: Peekable<std::slice::Iter<'a, Token>>,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [Token]) -> Self {
        Self {
            tokens: tokens.iter().peekable(),
        }
    }

    pub fn parse(mut self) -> ParseResult<BooleanExpr> {
        let mut original_tokens = self.tokens.clone();
        let exp = self
            .bool_expr(false)
            .map(|b| b.unwrap_or(BooleanExpr::EmptyExpression))?;

        match (self.tokens.len(), original_tokens.len()) {
            (0, _) => Ok(exp),
            (_, 3) => {
                let middle_token = original_tokens.nth(1).expect("iterator is 3 tokens long");
                if let Token::BinaryOp(_) = middle_token {
                    Err(ParseError::ExtraArgument(
                        self.tokens
                            .next()
                            .unwrap()
                            .as_os_string()
                            .quote()
                            .to_string(),
                    ))
                } else {
                    Err(ParseError::BinaryOperatorExpected(
                        middle_token.as_os_string().quote().to_string(),
                    ))
                }
            }
            (1, 2) => {
                let t = self
                    .tokens
                    .next()
                    .expect("iterator has exactly one more item");
                Err(ParseError::MissingArgument(
                    t.as_os_string().quote().to_string(),
                ))
            }
            _ => {
                let t = self
                    .tokens
                    .next()
                    .expect("if iterator was empty, first branch would be used");
                Err(ParseError::ExtraArgument(
                    t.as_os_string().quote().to_string(),
                ))
            }
        }
    }

    /// When inside a parenthesis, check if there is only one token
    /// In this case, no matter what that token it, we treat it as a lone
    /// literal and implicitly treat it like "-n <token>"
    fn check_single_token_in_parenthesis(&self) -> bool {
        // Use a clone of the iterator to be able to peek ahead multiple places
        let mut tokens = self.tokens.clone();
        matches!(tokens.next(), Some(t) if !matches!(t, Token::RParen))
            && matches!(tokens.next(), Some(Token::RParen))
    }

    /// Try to parse a boolean expression
    /// BOOL_EXPR → <SINGLE TOKEN>              # treated like a literal
    ///            | <None>                     # if could not match any BOOL_TERM
    ///            | BOOL_TERM (-a BOOL_TERM)*
    fn bool_expr(&mut self, in_parenthesis: bool) -> ParseResult<Option<BooleanExpr>> {
        if (!in_parenthesis && self.tokens.len() == 1)
            || (in_parenthesis && self.check_single_token_in_parenthesis())
        {
            return Ok(Some(BooleanExpr::UnaryStringOp(
                UnaryStringOp::NonZeroLength,
                self.str_expr().expect("there is a token"),
            )));
        }
        if in_parenthesis && matches!(self.tokens.peek(), Some(Token::RParen)) {
            return Ok(None);
        }
        if matches!(self.tokens.peek(), Some(Token::Negation)) {
            self.tokens.next(); // for '!'
            return Ok(self
                .bool_expr(in_parenthesis)?
                .map(|inner| BooleanExpr::Negation(Box::new(inner))));
        }
        let mut output = match self.bool_term()? {
            None => return Ok(None),
            Some(t) => t,
        };
        while let Some(Token::BinaryOp(BinaryOp::And)) = self.tokens.peek() {
            self.tokens.next();
            output = BooleanExpr::BinaryOp {
                left: Box::new(output),
                op: BinaryOp::And,
                right: Box::new(
                    self.bool_term()?
                        .ok_or_else(|| ParseError::MissingArgument("-a".quote().to_string()))?,
                ),
            }
        }
        Ok(Some(output))
    }

    /// Try to parse a boolean that can be "AND"-ed together
    /// BOOL_TERM → <None>                        # if could not match any BOOL_TERM2
    ///            | BOOL_TERM2 (-o BOOL_TERM2)*
    fn bool_term(&mut self) -> ParseResult<Option<BooleanExpr>> {
        let mut output = match self.bool_term2()? {
            Some(e) => e,
            None => return Ok(None),
        };

        while let Some(Token::BinaryOp(BinaryOp::Or)) = self.tokens.peek() {
            self.tokens.next();
            output = BooleanExpr::BinaryOp {
                left: Box::new(output),
                op: BinaryOp::Or,
                right: Box::new(
                    self.bool_term2()?
                        .ok_or_else(|| ParseError::MissingArgument("-o".quote().to_string()))?,
                ),
            }
        }
        Ok(Some(output))
    }

    /// Try to parse a boolean term
    /// BOOL_EXPR → LITERAL BINARY_STR_OP               # treated like a literal
    ///            | <None>                     # if could not match any BOOL_TERM
    ///            | BOOL_TERM (-a BOOL_TERM)*
    fn bool_term2(&mut self) -> ParseResult<Option<BooleanExpr>> {
        let initial_len = self.tokens.len();
        Ok(Some(match (self.tokens.next(), self.tokens.peek()) {
            (Some(Token::UnaryStringOp(op)), Some(t)) if initial_len == 2 => {
                let value = t.as_os_string().into_owned();
                let _ = self.tokens.next(); // consume second token
                BooleanExpr::UnaryStringOp(*op, value)
            }
            (Some(Token::Negation), Some(t)) if initial_len == 2 => {
                let value = t.as_os_string().into_owned();
                let _ = self.tokens.next(); // consume second token
                BooleanExpr::Negation(Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    value,
                )))
            }
            (Some(t), Some(Token::BinaryStringOp(op))) => {
                let _ = self.tokens.next(); // consume op

                let right = self.str_expr().ok_or_else(|| {
                    ParseError::MissingArgument(op.as_string_value().quote().to_string())
                })?;
                BooleanExpr::BinaryStringOp {
                    left: t.as_os_string().into_owned(),
                    op: op.clone(),
                    right,
                }
            }
            (Some(t), Some(Token::BinaryIntegerOp(op))) => {
                let _ = self.tokens.next(); // consume op
                let left = token_to_int(t)?;
                let right = self.int_expr()?.ok_or_else(|| {
                    ParseError::MissingArgument(op.as_string_value().quote().to_string())
                })?;
                BooleanExpr::BinaryIntegerOp {
                    left,
                    op: op.clone(),
                    right,
                }
            }
            (Some(Token::Literal(s)), _) => {
                BooleanExpr::UnaryStringOp(UnaryStringOp::NonZeroLength, s.clone())
            }
            (Some(Token::LParen), _) => {
                let mut tokens = self.tokens.clone();

                let output = self
                    .bool_expr(true)?
                    .ok_or_else(|| ParseError::MissingArgument(")".quote().to_string()))?;

                if let Some(Token::RParen) = self.tokens.next() {
                    output
                } else {
                    return Err(ParseError::MissingArgument(
                        tokens
                            .next_back()
                            .expect(
                                "next_back should never been none if self.bool_expr was not None",
                            )
                            .as_os_string()
                            .quote()
                            .to_string(),
                    ));
                }
            }
            (Some(Token::Negation), _) => BooleanExpr::Negation(Box::new(
                self.bool_term2()?
                    .ok_or_else(|| ParseError::MissingArgument("!".quote().to_string()))?,
            )),
            (Some(Token::UnaryStringOp(op)), _) => self
                .str_expr()
                .map(|s| BooleanExpr::UnaryStringOp(*op, s))
                .ok_or_else(|| {
                    ParseError::MissingArgument(op.as_string_value().quote().to_string())
                })?,
            (Some(Token::StringLength), _) => {
                let left = self
                    .str_expr()
                    .ok_or_else(|| ParseError::UnaryOperatorExpected("'-l'".to_string()))?;
                let op = if let Some(Token::BinaryIntegerOp(op)) = self.tokens.next() {
                    op
                } else {
                    return Err(ParseError::UnaryOperatorExpected("'-l'".to_string()));
                };
                let right = self
                    .int_expr()?
                    .ok_or_else(|| ParseError::BinaryOperatorExpected(left.quote().to_string()))?;
                BooleanExpr::BinaryIntegerOp {
                    left: IntegerExpr::Length(left),
                    op: *op,
                    right,
                }
            }
            (Some(Token::BinaryOp(op)), _) => {
                return Err(ParseError::UnaryOperatorExpected(
                    op.as_string_value().quote().to_string(),
                ));
            }
            (None, _) => return Ok(None),
            ts => todo!("haven't implemented {:?}", ts),
        }))

        // Ok(Some(match self.tokens.next() {
        //     Some(Token::Literal(s))
        //         if !matches!(self.tokens.peek(), Some(Token::BinaryStringOp(_)))
        //             && !matches!(self.tokens.peek(), Some(Token::BinaryIntegerOp(_))) =>
        //     {
        //         BooleanExpr::UnaryStringOp(UnaryStringOp::NonZeroLength, s.clone())
        //     }
        //     Some(Token::LParen) => {
        //         let mut tokens = self.tokens.clone();
        //
        //         let output = self.bool_expr(true)?
        //             .ok_or_else(|| ParseError::MissingArgument(")".quote().to_string()))?;
        //
        //         if let Some(Token::RParen) = self.tokens.next() {
        //             output
        //         } else {
        //             return Err(ParseError::MissingArgument(tokens.next_back().expect("next_back should never been none if self.bool_expr was not None").as_os_string().quote().to_string()))
        //         }
        //     }
        //     Some(Token::Negation) => BooleanExpr::Negation(Box::new(
        //         self.bool_term2()?
        //             .ok_or_else(|| ParseError::MissingArgument("!".quote().to_string()))?,
        //     )),
        //     Some(Token::UnaryStringOp(op)) => self.str_expr().map(|s| BooleanExpr::UnaryStringOp(*op, s)).ok_or_else(|| ParseError::MissingArgument(op.as_string_value().quote().to_string()))?,
        //     Some(Token::Literal(s)) => match self.tokens.next() {
        //         Some(Token::BinaryStringOp(op)) => BooleanExpr::BinaryStringOp {
        //             left: s.clone(),
        //             op: *op,
        //             right: self.str_expr().ok_or_else(|| ParseError::MissingArgument(op.as_string_value().quote().to_string()))?,
        //         },
        //         Some(Token::BinaryIntegerOp(op)) => BooleanExpr::BinaryIntegerOp {
        //             left: IntegerExpr::Integer(
        //                 s.to_str().and_then(|x| x.parse().ok()).ok_or_else(||
        //                     ParseError::InvalidInteger(s.to_string_lossy().to_string()))?,
        //             ),
        //             op: *op,
        //             right: self.int_expr()?.ok_or_else(|| ParseError::MissingArgument(op.as_string_value().quote().to_string()))?,
        //         },
        //         _ => unreachable!("not possible due to first condition in bool_term2's branches"),
        //     },
        //     Some(Token::StringLength) => {
        //         let left = self.str_expr().ok_or_else(|| ParseError::UnaryOperatorExpected("'-l'".to_string()))?;
        //         let op = if let Some(Token::BinaryIntegerOp(op)) = self.tokens.next() {
        //             op
        //         } else {
        //             return Err(ParseError::UnaryOperatorExpected("'-l'".to_string()));
        //         };
        //         let right = self.int_expr()?.ok_or_else(|| ParseError::BinaryOperatorExpected(left.quote().to_string()))?;
        //         BooleanExpr::BinaryIntegerOp {
        //             left: IntegerExpr::Length(left),
        //             op: *op,
        //             right,
        //         }
        //     }
        //     Some(Token::BinaryOp(op)) => {
        //         return Err(ParseError::UnaryOperatorExpected(op.as_string_value().quote().to_string()));
        //     }
        //     None => return Ok(None),
        //     t => todo!("haven't implemented {:?}", t),
        // }))
    }

    fn int_expr(&mut self) -> ParseResult<Option<IntegerExpr>> {
        match self.tokens.next() {
            Some(Token::Literal(s)) => Ok(Some(IntegerExpr::Integer(
                s.to_str().expect("todo").parse().expect("todo"),
            ))),
            Some(Token::StringLength) => self
                .str_expr()
                .map(|s| IntegerExpr::Length(s))
                .map(|x| Some(x))
                .ok_or_else(|| ParseError::InvalidInteger("'-l'".to_string())),
            Some(t) => Err(ParseError::InvalidInteger(
                t.as_os_string().quote().to_string(),
            )),
            None => Ok(None),
        }
    }

    fn str_expr(&mut self) -> Option<StringExpr> {
        self.tokens.next().map(|t| t.as_os_string().into_owned())
    }
}

fn token_to_int(t: &Token) -> ParseResult<IntegerExpr> {
    match t {
        Token::Literal(s) => s
            .to_str()
            .and_then(|x| x.parse().ok())
            .map(|x| IntegerExpr::Integer(x))
            .ok_or_else(|| ParseError::InvalidInteger(s.quote().to_string())),
        t => Err(ParseError::InvalidInteger(
            t.as_os_string().quote().to_string(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use crate::error::ParseError;
    use crate::lexer::{BinaryIntegerOp, BinaryOp, BinaryStringOp, Token, UnaryStringOp};
    use crate::parserv2::{token_to_int, BooleanExpr, IntegerExpr, Parser};

    #[test]
    fn simple_parsing() {
        assert_eq!(
            Parser::new(&vec![Token::Literal("true".into())]).parse(),
            Ok(BooleanExpr::UnaryStringOp(
                UnaryStringOp::NonZeroLength,
                "true".into()
            ))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::LParen,
                Token::Literal("true".into()),
                Token::RParen
            ])
            .parse(),
            Ok(BooleanExpr::UnaryStringOp(
                UnaryStringOp::NonZeroLength,
                "true".into()
            ))
        );

        assert_eq!(
            Parser::new(&vec![Token::Negation, Token::Literal("true".into())]).parse(),
            Ok(BooleanExpr::Negation(Box::new(BooleanExpr::UnaryStringOp(
                UnaryStringOp::NonZeroLength,
                "true".into()
            ))))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("c".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::Literal("d".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryOp {
                left: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "c".into()
                )),
                op: BinaryOp::And,
                right: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "d".into()
                )),
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::Or),
                Token::Literal("b".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryOp {
                left: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "a".into()
                )),
                op: BinaryOp::Or,
                right: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "b".into()
                )),
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::UnaryStringOp(UnaryStringOp::NonZeroLength),
                Token::Literal("true".into())
            ])
            .parse(),
            Ok(BooleanExpr::UnaryStringOp(
                UnaryStringOp::NonZeroLength,
                "true".into()
            ))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::UnaryStringOp(UnaryStringOp::ZeroLength),
                Token::Literal("true".into())
            ])
            .parse(),
            Ok(BooleanExpr::UnaryStringOp(
                UnaryStringOp::ZeroLength,
                "true".into()
            ))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("true".into()),
                Token::BinaryStringOp(BinaryStringOp::Equals),
                Token::Literal("false".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryStringOp {
                left: "true".into(),
                op: BinaryStringOp::Equals,
                right: "false".into()
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("on".into()),
                Token::BinaryStringOp(BinaryStringOp::NotEquals),
                Token::Literal("off".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryStringOp {
                left: "on".into(),
                op: BinaryStringOp::NotEquals,
                right: "off".into()
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("1".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Equals),
                Token::Literal("2".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryIntegerOp {
                left: IntegerExpr::Integer(1),
                op: BinaryIntegerOp::Equals,
                right: IntegerExpr::Integer(2),
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("3".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::GreaterOrEqual),
                Token::Literal("4".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryIntegerOp {
                left: IntegerExpr::Integer(3),
                op: BinaryIntegerOp::GreaterOrEqual,
                right: IntegerExpr::Integer(4),
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("5".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
                Token::Literal("6".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryIntegerOp {
                left: IntegerExpr::Integer(5),
                op: BinaryIntegerOp::Greater,
                right: IntegerExpr::Integer(6),
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("7".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::LessThanOrEqual),
                Token::Literal("8".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryIntegerOp {
                left: IntegerExpr::Integer(7),
                op: BinaryIntegerOp::LessThanOrEqual,
                right: IntegerExpr::Integer(8),
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("9".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::LessThan),
                Token::Literal("10".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryIntegerOp {
                left: IntegerExpr::Integer(9),
                op: BinaryIntegerOp::LessThan,
                right: IntegerExpr::Integer(10),
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("11".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::NotEquals),
                Token::Literal("12".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryIntegerOp {
                left: IntegerExpr::Integer(11),
                op: BinaryIntegerOp::NotEquals,
                right: IntegerExpr::Integer(12),
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::StringLength,
                Token::Literal("hippopotomonstrosesquippedaliophobia".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
                Token::Literal("4".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryIntegerOp {
                left: IntegerExpr::Length("hippopotomonstrosesquippedaliophobia".into()),
                op: BinaryIntegerOp::Greater,
                right: IntegerExpr::Integer(4),
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("4".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
                Token::StringLength,
                Token::Literal("hippopotomonstrosesquippedaliophobia".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryIntegerOp {
                left: IntegerExpr::Integer(4),
                op: BinaryIntegerOp::Greater,
                right: IntegerExpr::Length("hippopotomonstrosesquippedaliophobia".into()),
            })
        );
    }

    #[test]
    fn left_associativity() {
        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::Literal("b".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::Literal("c".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryOp {
                left: Box::new(BooleanExpr::BinaryOp {
                    left: Box::new(BooleanExpr::UnaryStringOp(
                        UnaryStringOp::NonZeroLength,
                        "a".into()
                    )),
                    op: BinaryOp::And,
                    right: Box::new(BooleanExpr::UnaryStringOp(
                        UnaryStringOp::NonZeroLength,
                        "b".into()
                    )),
                }),
                op: BinaryOp::And,
                right: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "c".into()
                )),
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::Or),
                Token::Literal("b".into()),
                Token::BinaryOp(BinaryOp::Or),
                Token::Literal("c".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryOp {
                left: Box::new(BooleanExpr::BinaryOp {
                    left: Box::new(BooleanExpr::UnaryStringOp(
                        UnaryStringOp::NonZeroLength,
                        "a".into()
                    )),
                    op: BinaryOp::Or,
                    right: Box::new(BooleanExpr::UnaryStringOp(
                        UnaryStringOp::NonZeroLength,
                        "b".into()
                    )),
                }),
                op: BinaryOp::Or,
                right: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "c".into()
                )),
            })
        );
    }

    #[test]
    fn binary_precedence() {
        assert_eq!(
            Parser::new(&vec![
                Token::Literal("".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::Literal("true".into()),
                Token::BinaryOp(BinaryOp::Or),
                Token::Literal("true".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryOp {
                left: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "".into()
                )),
                op: BinaryOp::And,
                right: Box::new(BooleanExpr::BinaryOp {
                    left: Box::new(BooleanExpr::UnaryStringOp(
                        UnaryStringOp::NonZeroLength,
                        "true".into()
                    )),
                    op: BinaryOp::Or,
                    right: Box::new(BooleanExpr::UnaryStringOp(
                        UnaryStringOp::NonZeroLength,
                        "true".into()
                    )),
                })
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("".into()),
                Token::BinaryOp(BinaryOp::Or),
                Token::Literal("true".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::Literal("true".into())
            ])
            .parse(),
            Ok(BooleanExpr::BinaryOp {
                left: Box::new(BooleanExpr::BinaryOp {
                    left: Box::new(BooleanExpr::UnaryStringOp(
                        UnaryStringOp::NonZeroLength,
                        "".into()
                    )),
                    op: BinaryOp::Or,
                    right: Box::new(BooleanExpr::UnaryStringOp(
                        UnaryStringOp::NonZeroLength,
                        "true".into()
                    )),
                }),
                op: BinaryOp::And,
                right: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "true".into()
                )),
            })
        );
    }

    #[test]
    fn negation_entire_or_expression() {
        assert_eq!(
            Parser::new(&vec![
                Token::Negation,
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::Or),
                Token::Literal("b".into()),
            ])
            .parse(),
            Ok(BooleanExpr::Negation(Box::new(BooleanExpr::BinaryOp {
                left: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "a".into()
                )),
                op: BinaryOp::Or,
                right: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "b".into()
                )),
            }))),
        );
    }

    #[test]
    fn negation_has_lower_precedence_than_operators() {
        assert_eq!(
            Parser::new(&vec![
                // '!' '(' '!' '!' a -o '!' a ')'
                Token::Negation,
                Token::LParen,
                Token::Negation,
                Token::Negation,
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::Or),
                Token::Negation,
                Token::Literal("a".into()),
                Token::RParen
            ])
            .parse(),
            Ok(BooleanExpr::Negation(Box::new(BooleanExpr::Negation(
                Box::new(BooleanExpr::Negation(Box::new(BooleanExpr::BinaryOp {
                    left: Box::new(BooleanExpr::UnaryStringOp(
                        UnaryStringOp::NonZeroLength,
                        "a".into()
                    )),
                    op: BinaryOp::Or,
                    right: Box::new(BooleanExpr::Negation(Box::new(BooleanExpr::UnaryStringOp(
                        UnaryStringOp::NonZeroLength,
                        "a".into()
                    )))),
                })))
            )))),
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
    #[case::string_length(Token::StringLength, "-l")]
    fn turn_syntax_to_string(#[case] token: Token, #[case] expected: &str) {
        assert_eq!(
            Parser::new(&vec![
                Token::UnaryStringOp(UnaryStringOp::NonZeroLength),
                token.clone()
            ])
            .parse(),
            Ok(BooleanExpr::UnaryStringOp(
                UnaryStringOp::NonZeroLength,
                expected.into()
            ))
        );

        assert_eq!(
            Parser::new(&vec![Token::Negation, token]).parse(),
            Ok(BooleanExpr::Negation(Box::new(BooleanExpr::UnaryStringOp(
                UnaryStringOp::NonZeroLength,
                expected.into()
            ))))
        );
    }

    #[test]
    fn missing_arg() {
        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::Or)
            ])
            .parse(),
            Err(ParseError::MissingArgument("'-o'".into()))
        );
        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::And)
            ])
            .parse(),
            Err(ParseError::MissingArgument("'-a'".into()))
        );
        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::Negation
            ])
            .parse(),
            Err(ParseError::MissingArgument("'!'".into()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::BinaryOp(BinaryOp::Or),
                Token::Literal("a".into()),
            ])
            .parse(),
            Err(ParseError::UnaryOperatorExpected("'-o'".into())),
        );

        assert_eq!(
            Parser::new(&vec![
                Token::BinaryOp(BinaryOp::And),
                Token::Literal("a".into()),
            ])
            .parse(),
            Err(ParseError::UnaryOperatorExpected("'-a'".into())),
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::UnaryStringOp(UnaryStringOp::ZeroLength)
            ])
            .parse(),
            Err(ParseError::MissingArgument("'-z'".into()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("5".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Equals),
            ])
            .parse(),
            Err(ParseError::MissingArgument("'-eq'".into()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::StringLength,
            ])
            .parse(),
            Err(ParseError::UnaryOperatorExpected("'-l'".into()))
        );

        assert_eq!(
            Parser::new(&vec![Token::StringLength, Token::Literal("a".into())]).parse(),
            Err(ParseError::UnaryOperatorExpected("'-l'".into())),
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::BinaryStringOp(BinaryStringOp::Equals)
            ])
            .parse(),
            Err(ParseError::MissingArgument("'='".to_string())),
        );
    }

    //See https://github.com/uutils/coreutils/issues/6203
    #[test]
    fn complex_missing_args() {
        assert_eq!(
            Parser::new(&vec![
                Token::Literal("x".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::LParen,
                Token::BinaryOp(BinaryOp::Or),
                Token::Literal("asd".into()),
                Token::RParen,
                Token::BinaryOp(BinaryOp::And),
                Token::Literal("y".into()),
            ])
            .parse(),
            Err(ParseError::UnaryOperatorExpected("'-o'".into())),
        );

        assert_eq!(
            Parser::new(&vec![
                Token::BinaryOp(BinaryOp::And),
                Token::LParen,
                Token::Literal("x".into()),
                Token::BinaryOp(BinaryOp::Or),
                Token::Literal("asd".into()),
                Token::RParen,
                Token::BinaryOp(BinaryOp::And),
                Token::Literal("y".into()),
            ])
            .parse(),
            Err(ParseError::UnaryOperatorExpected("'-a'".into())),
        );
    }
    #[test]
    fn invalid_integers() {
        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
                Token::Literal("4".into()),
            ])
            .parse(),
            Err(ParseError::InvalidInteger("'a'".into()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("4".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
                Token::StringLength,
            ])
            .parse(),
            Err(ParseError::InvalidInteger("'-l'".into()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("4".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
                Token::RParen,
            ])
            .parse(),
            Err(ParseError::InvalidInteger("')'".into()))
        );
    }

    // Test code path where we expect an integer but get something that can't even be treated
    // like a &str. This test only runs on Linux because what values are allowed in an
    // OsString is OS-specific.
    //
    // This is ignored because uucore::quoting_style::escape_name does not handle non-UTF8
    // characters correctly - it calls to_string_lossy instead of converting the bytes into octal.
    #[ignore]
    #[cfg(target_os = "linux")]
    #[test]
    fn invalid_non_utf8_integer() {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt;

        assert_eq!(
            Parser::new(&vec![
                Token::Literal(OsString::from_vec(vec![255])),
                Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
                Token::Literal("4".into()),
            ])
            .parse(),
            Err(ParseError::InvalidInteger(r"\377".into()))
        );
    }

    #[test]
    fn string_length_as_string() {
        assert_eq!(
            Parser::new(&vec![Token::StringLength]).parse(),
            Ok(BooleanExpr::UnaryStringOp(
                UnaryStringOp::NonZeroLength,
                "-l".into()
            ))
        );
        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::LParen,
                Token::StringLength,
                Token::RParen
            ])
            .parse(),
            Ok(BooleanExpr::BinaryOp {
                left: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "a".into()
                )),
                op: BinaryOp::And,
                right: Box::new(BooleanExpr::UnaryStringOp(
                    UnaryStringOp::NonZeroLength,
                    "-l".into()
                )),
            })
        );
    }

    #[test]
    fn empty_parenthesis() {
        assert_eq!(
            Parser::new(&vec![Token::LParen, Token::RParen]).parse(),
            Err(ParseError::MissingArgument("')'".to_string()))
        );
    }

    #[test]
    fn empty_tokens() {
        assert_eq!(
            Parser::new(&Vec::new()).parse(),
            Ok(BooleanExpr::EmptyExpression),
        );
    }

    #[test]
    fn missing_closing_parenthesis() {
        assert_eq!(
            Parser::new(&vec![Token::LParen, Token::Literal("a".into())]).parse(),
            Err(ParseError::MissingArgument("'a'".to_string()))
        );
    }

    #[test]
    fn many_literals() {
        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::Literal("b".into())
            ])
            .parse(),
            Err(ParseError::MissingArgument("'b'".to_string()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::Literal("b".into()),
                Token::Literal("c".into())
            ])
            .parse(),
            Err(ParseError::BinaryOperatorExpected("'b'".to_string()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::Literal("b".into()),
                Token::Literal("c".into()),
                Token::Literal("d".into())
            ])
            .parse(),
            Err(ParseError::ExtraArgument("'b'".to_string()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("a".into()),
                Token::Literal("b".into()),
                Token::Literal("c".into()),
                Token::Literal("d".into()),
                Token::Literal("e".into())
            ])
            .parse(),
            Err(ParseError::ExtraArgument("'b'".to_string()))
        );
    }

    #[test]
    fn many_unary_arg() {
        assert_eq!(
            Parser::new(&vec![Token::UnaryStringOp(UnaryStringOp::ZeroLength)]).parse(),
            Ok(BooleanExpr::UnaryStringOp(
                UnaryStringOp::NonZeroLength,
                "-z".into()
            ))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::UnaryStringOp(UnaryStringOp::ZeroLength),
                Token::UnaryStringOp(UnaryStringOp::ZeroLength)
            ])
            .parse(),
            Ok(BooleanExpr::UnaryStringOp(
                UnaryStringOp::ZeroLength,
                "-z".into()
            ))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::UnaryStringOp(UnaryStringOp::ZeroLength),
                Token::UnaryStringOp(UnaryStringOp::ZeroLength),
                Token::UnaryStringOp(UnaryStringOp::ZeroLength)
            ])
            .parse(),
            Err(ParseError::BinaryOperatorExpected("'-z'".to_string()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::UnaryStringOp(UnaryStringOp::ZeroLength),
                Token::UnaryStringOp(UnaryStringOp::ZeroLength),
                Token::UnaryStringOp(UnaryStringOp::ZeroLength),
                Token::UnaryStringOp(UnaryStringOp::ZeroLength)
            ])
            .parse(),
            Err(ParseError::ExtraArgument("'-z'".to_string()))
        );
    }

    #[test]
    fn many_binary_args() {
        assert_eq!(
            Parser::new(&vec![
                Token::BinaryOp(BinaryOp::And),
                Token::BinaryOp(BinaryOp::Or)
            ])
            .parse(),
            Err(ParseError::UnaryOperatorExpected("'-a'".to_string()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::BinaryOp(BinaryOp::And),
                Token::BinaryOp(BinaryOp::Or),
                Token::BinaryOp(BinaryOp::Or)
            ])
            .parse(),
            Err(ParseError::UnaryOperatorExpected("'-a'".to_string()))
        );
    }

    // A few cases that don't quite fall into other cases
    #[test]
    fn odd_balls() {
        assert_eq!(
            Parser::new(&vec![
                Token::UnaryStringOp(UnaryStringOp::NonZeroLength),
                Token::Literal("42".into()),
                Token::LParen
            ])
            .parse(),
            Err(ParseError::BinaryOperatorExpected("'42'".to_string()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::UnaryStringOp(UnaryStringOp::NonZeroLength),
                Token::BinaryOp(BinaryOp::And),
                Token::LParen
            ])
            .parse(),
            Err(ParseError::ExtraArgument("'('".to_string()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::UnaryStringOp(UnaryStringOp::NonZeroLength),
                Token::BinaryOp(BinaryOp::And),
                Token::LParen,
                Token::Negation
            ])
            .parse(),
            Err(ParseError::ExtraArgument("'('".to_string()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("x".into()),
                Token::BinaryOp(BinaryOp::And),
                Token::LParen,
                Token::BinaryOp(BinaryOp::Or),
                Token::Literal("x".into()),
                Token::RParen,
                Token::BinaryOp(BinaryOp::And),
                Token::Literal("x".into())
            ])
            .parse(),
            Err(ParseError::UnaryOperatorExpected("'-o'".to_string()))
        );

        assert_eq!(
            Parser::new(&vec![
                Token::StringLength,
                Token::Literal("x".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Equals)
            ])
            .parse(),
            Err(ParseError::BinaryOperatorExpected("'x'".to_string())),
        );

        assert_eq!(
            Parser::new(&vec![
                Token::BinaryOp(BinaryOp::Or),
                Token::BinaryStringOp(BinaryStringOp::Equals),
                Token::BinaryOp(BinaryOp::Or),
            ])
            .parse(),
            Ok(BooleanExpr::BinaryStringOp {
                left: "-o".into(),
                op: BinaryStringOp::Equals,
                right: "-o".into(),
            })
        );
    }

    #[test]
    fn non_boolean_binary_operations_with_different_types() {
        assert_eq!(
            Parser::new(&vec![
                Token::StringLength,
                Token::BinaryStringOp(BinaryStringOp::Equals),
                Token::StringLength,
            ])
            .parse(),
            Ok(BooleanExpr::BinaryStringOp {
                left: "-l".into(),
                op: BinaryStringOp::Equals,
                right: "-l".into(),
            })
        );

        assert_eq!(
            Parser::new(&vec![
                Token::BinaryOp(BinaryOp::Or),
                Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
                Token::BinaryOp(BinaryOp::Or),
            ])
            .parse(),
            Err(ParseError::InvalidInteger("'-o'".into())),
        );

        assert_eq!(
            Parser::new(&vec![
                Token::Literal("4".into()),
                Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
                Token::BinaryOp(BinaryOp::Or),
            ])
            .parse(),
            Err(ParseError::InvalidInteger("'-o'".into())),
        );

        assert_eq!(
            Parser::new(&vec![
                Token::BinaryOp(BinaryOp::Or),
                Token::BinaryIntegerOp(BinaryIntegerOp::Greater),
                Token::Literal("4".into()),
            ])
            .parse(),
            Err(ParseError::InvalidInteger("'-o'".into())),
        );
    }

    #[test]
    fn test_token_to_int() {
        assert_eq!(
            token_to_int(&Token::Literal("-4".into())),
            Ok(IntegerExpr::Integer(-4)),
        );
        assert_eq!(
            token_to_int(&Token::Literal("negative 4".into())),
            Err(ParseError::InvalidInteger("'negative 4'".to_string())),
        );
        assert_eq!(
            token_to_int(&Token::LParen),
            Err(ParseError::InvalidInteger("'('".to_string())),
        );
    }
}
