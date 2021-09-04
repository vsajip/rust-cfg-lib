//
//  Copyright (C) 2018-2021 Red Dove Consultants Limited
//
/*!
  This module implements code to tokenize and parse CFG source text, and query configurations.
*/
use std::cell::RefCell;
use std::cmp::{Ord, Ordering};
use std::collections::{HashMap, HashSet};
use std::convert::{From, TryInto};
use std::env;
use std::fmt::{self, Write};
use std::fs::{canonicalize, File};
use std::io::{self, BufRead, BufReader, Cursor, Error, ErrorKind, Read, Result};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::result::Result as StdResult;

use chrono::{DateTime, FixedOffset, NaiveDate, NaiveDateTime, NaiveTime};
use lazy_static::lazy_static;
use num_complex::Complex64;
use regex::{Captures, Regex};

//
// Low level I/O stuff
//

const UTF8_ACCEPT: u32 = 0;
const UTF8_REJECT: u32 = 12;

lazy_static! {
    // see http://bjoern.hoehrmann.de/utf-8/decoder/dfa/
    /*
      // The first part of the table maps bytes to character classes that
      // to reduce the size of the transition table and create bit-masks.
       0   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
      32   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
      64   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
      96   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
     128   1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,  9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
     160   7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,  7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
     192   8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2,  2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
     224  10,3,3,3,3,3,3,3,3,3,3,3,3,4,3,3, 11,6,6,6,5,8,8,8,8,8,8,8,8,8,8,8,

          // The second part is a transition table that maps a combination
          // of a state of the automaton and a character class to a state.
     256   0,12,24,36,60,96,84,12,12,12,48,72, 12,12,12,12,12,12,12,12,12,12,12,12,
     280  12, 0,12,12,12,12,12, 0,12, 0,12,12, 12,24,12,12,12,12,12,24,12,24,12,12,
     304  12,12,12,12,12,12,12,24,12,12,12,12, 12,24,12,12,12,12,12,12,12,24,12,12,
     328  12,12,12,12,12,12,12,36,12,36,12,12, 12,36,12,12,12,12,12,36,12,36,12,12,
     352  12,36,12,12,12,12,12,12,12,12,12,12,

    uint32_t inline
    decode(uint32_t* state, uint32_t* code_point, uint32_t byte) {
      uint32_t type = utf8d[byte];

      *code_point = (*state != UTF8_ACCEPT) ?
        (byte & 0x3fu) | (*code_point << 6) :
        (0xff >> type) & (byte);

      *state = utf8d[256 + *state + type];
      return *state;
    }

     */

    static ref UTF8_LOOKUP: [u8; 364] = {
        let mut map = [0u8; 364];
        for i in 128..144 {
            map[i] = 1;
        }
        for i in 144..160 {
            map[i] = 9;
        }
        for i in 160..192 {
            map[i] = 7;
        }
        map[192] = 8;
        map[193] = 8;
        for i in 194..224 {
            map[i] = 2;
        }
        map[224] = 10;
        for i in 225..240 {
            map[i] = 3;
        }
        map[237] = 4;
        map[240] = 11;
        for i in 241..244 {
            map[i] = 6;
        }
        map[244] = 5;
        for i in 245..256 {
            map[i] = 8;
        }
        for i in 256..260 {
            map[i] = ((i - 256) * 12) as u8;
        }
        map[260] = 60;
        map[261] = 96;
        map[262] = 84;
        for i in 263..364 {
            map[i] = 12;
        }
        map[266] = 48;
        map[267] = 72;
        map[281] = 0;
        map[287] = 0;
        map[289] = 0;
        map[293] = 24;
        map[299] = 24;
        map[301] = 24;
        map[311] = 24;
        map[317] = 24;
        map[325] = 24;
        map[335] = 36;
        map[337] = 36;
        map[341] = 36;
        map[347] = 36;
        map[349] = 36;
        map[353] = 36;
        map
    };

    static ref PUNCTUATION: HashMap<char, TokenKind> = {
        let mut map = HashMap::new();

        map.insert(':', TokenKind::Colon);
        map.insert('-', TokenKind::Minus);
        map.insert('+', TokenKind::Plus);
        map.insert('*', TokenKind::Star);
        map.insert('/', TokenKind::Slash);
        map.insert('%', TokenKind::Modulo);
        map.insert(',', TokenKind::Comma);
        map.insert('{', TokenKind::LeftCurly);
        map.insert('}', TokenKind::RightCurly);
        map.insert('[', TokenKind::LeftBracket);
        map.insert(']', TokenKind::RightBracket);
        map.insert('(', TokenKind::LeftParenthesis);
        map.insert(')', TokenKind::RightParenthesis);
        map.insert('@', TokenKind::At);
        map.insert('$', TokenKind::Dollar);
        map.insert('<', TokenKind::LessThan);
        map.insert('>', TokenKind::GreaterThan);
        map.insert('!', TokenKind::Not);
        map.insert('~', TokenKind::BitwiseComplement);
        map.insert('&', TokenKind::BitwiseAnd);
        map.insert('|', TokenKind::BitwiseOr);
        map.insert('^', TokenKind::BitwiseXor);
        map.insert('.', TokenKind::Dot);
        map
    };

    static ref KEYWORDS: HashMap<String, TokenKind> = {
        let mut map = HashMap::new();

        map.insert("true".to_string(), TokenKind::True);
        map.insert("false".to_string(), TokenKind::False);
        map.insert("null".to_string(), TokenKind::None);
        map.insert("is".to_string(), TokenKind::Is);
        map.insert("in".to_string(), TokenKind::In);
        map.insert("not".to_string(), TokenKind::Not);
        map.insert("and".to_string(), TokenKind::And);
        map.insert("or".to_string(), TokenKind::Or);
        map
    };

    static ref KEYWORD_VALUES: HashMap<String, ScalarValue> = {
        let mut map = HashMap::new();

        map.insert("true".to_string(), ScalarValue::Bool(true));
        map.insert("false".to_string(), ScalarValue::Bool(false));
        map.insert("null".to_string(), ScalarValue::Null);
        map
    };

    static ref EXPRESSION_STARTERS: HashSet<TokenKind> = {
        let mut set = HashSet::new();

        set.insert(TokenKind::LeftCurly);
        set.insert(TokenKind::LeftCurly);
        set.insert(TokenKind::LeftBracket);
        set.insert(TokenKind::LeftParenthesis);
        set.insert(TokenKind::At);
        set.insert(TokenKind::Dollar);
        set.insert(TokenKind::BackTick);
        set.insert(TokenKind::Plus);
        set.insert(TokenKind::Minus);
        set.insert(TokenKind::BitwiseComplement);
        set.insert(TokenKind::Number);
        set.insert(TokenKind::Complex);
        set.insert(TokenKind::True);
        set.insert(TokenKind::False);
        set.insert(TokenKind::None);
        set.insert(TokenKind::Not);
        set.insert(TokenKind::String);
        set.insert(TokenKind::Word);
        set
    };

    static ref VALUE_STARTERS: HashSet<TokenKind> = {
        let mut set = HashSet::new();

        set.insert(TokenKind::Word);
        set.insert(TokenKind::Number);
        set.insert(TokenKind::Complex);
        set.insert(TokenKind::String);
        set.insert(TokenKind::BackTick);
        set.insert(TokenKind::None);
        set.insert(TokenKind::True);
        set.insert(TokenKind::False);
        set
    };

    static ref COMPARISON_OPERATORS: HashSet<TokenKind> = {
        let mut set = HashSet::new();

        set.insert(TokenKind::LessThan);
        set.insert(TokenKind::LessThanOrEqual);
        set.insert(TokenKind::GreaterThan);
        set.insert(TokenKind::GreaterThanOrEqual);
        set.insert(TokenKind::Equal);
        set.insert(TokenKind::Unequal);
        set.insert(TokenKind::AltUnequal);
        set.insert(TokenKind::Is);
        set.insert(TokenKind::In);
        set.insert(TokenKind::Not);
        set
    };

    static ref ESCAPES: HashMap<char, char> = {
        let mut map = HashMap::new();

        map.insert('a', '\u{0007}');
        map.insert('b', '\u{0008}');
        map.insert('f', '\u{000C}');
        map.insert('n', '\n');
        map.insert('r', '\r');
        map.insert('t', '\t');
        map.insert('v', '\u{000B}');
        map.insert('\\', '\\');
        map.insert('\'', '\'');
        map.insert('"', '"');
        map
    };

    static ref TOKEN_TEXT: HashMap<TokenKind, String> = {
        let mut map = HashMap::new();

        map.insert(TokenKind::EOF, "EOF".to_string());
        map.insert(TokenKind::Word, "<an identifier>".to_string());
        map.insert(TokenKind::Number, "<a number>".to_string());
        map.insert(TokenKind::String, "<a literal string>".to_string());
        map.insert(TokenKind::Newline, "<a newline>".to_string());
        map.insert(TokenKind::LeftCurly, "'{'".to_string());
        map.insert(TokenKind::RightCurly, "'}'".to_string());
        map.insert(TokenKind::LeftBracket, "'['".to_string());
        map.insert(TokenKind::RightBracket, "']'".to_string());
        map.insert(TokenKind::LeftParenthesis, "'('".to_string());
        map.insert(TokenKind::RightParenthesis, "')'".to_string());
        map.insert(TokenKind::LessThan, "'<'".to_string());
        map.insert(TokenKind::GreaterThan, "'>'".to_string());
        map.insert(TokenKind::LessThanOrEqual, "'<='".to_string());
        map.insert(TokenKind::GreaterThanOrEqual, "'>='".to_string());
        map.insert(TokenKind::Assign, "'='".to_string());
        map.insert(TokenKind::Equal, "'=='".to_string());
        map.insert(TokenKind::Unequal, "'!='".to_string());
        map.insert(TokenKind::AltUnequal, "'<>'".to_string());
        map.insert(TokenKind::LeftShift, "'<<'".to_string());
        map.insert(TokenKind::RightShift, "'>>'".to_string());
        map.insert(TokenKind::Dot, "'.'".to_string());
        map.insert(TokenKind::Comma, "','".to_string());
        map.insert(TokenKind::Colon, "':'".to_string());
        map.insert(TokenKind::At, "'@'".to_string());
        map.insert(TokenKind::Plus, "'+'".to_string());
        map.insert(TokenKind::Minus, "'-'".to_string());
        map.insert(TokenKind::Star, "'*'".to_string());
        map.insert(TokenKind::Power, "'**'".to_string());
        map.insert(TokenKind::Slash, "'/'".to_string());
        map.insert(TokenKind::SlashSlash, "'//'".to_string());
        map.insert(TokenKind::Modulo, "'%'".to_string());
        map.insert(TokenKind::BackTick, "'`'".to_string());
        map.insert(TokenKind::Dollar, "'$'".to_string());
        map.insert(TokenKind::True, "<true>".to_string());
        map.insert(TokenKind::False, "<false>".to_string());
        map.insert(TokenKind::None, "<none>".to_string());
        map.insert(TokenKind::Is, "'is'".to_string());
        map.insert(TokenKind::In, "'in'".to_string());
        map.insert(TokenKind::Not, "'not'".to_string());
        map.insert(TokenKind::And, "'and'".to_string());
        map.insert(TokenKind::Or, "'or'".to_string());
        map.insert(TokenKind::BitwiseAnd, "'&'".to_string());
        map.insert(TokenKind::BitwiseOr, "'|'".to_string());
        map.insert(TokenKind::BitwiseXor, "'^'".to_string());
        map.insert(TokenKind::BitwiseComplement, "'~'".to_string());
        map.insert(TokenKind::Complex, "<complex>".to_string());
        map.insert(TokenKind::IsNot, "'is not'".to_string());
        map.insert(TokenKind::NotIn, "'not in'".to_string());
        map
    };

    static ref IDENTIFIER_PATTERN: Regex = Regex::new(r"^[\pL_](\w*)$").expect("couldn't compile regex");
    static ref ISO_DATETIME_PATTERN: Regex = Regex::new(r"^(\d{4})-(\d{2})-(\d{2})(([ T])(((\d{2}):(\d{2}):(\d{2}))(\.\d{1,6})?(([+-])(\d{2}):(\d{2})(:(\d{2})(\.\d{1,6})?)?)?))?$").expect("couldn't compile regex");
    static ref ENV_VALUE_PATTERN: Regex = Regex::new(r"^\$(\w+)(\|(.*))?$").expect("couldn't compile regex");
    static ref INTERPOLATION_PATTERN: Regex = Regex::new(r"\$\{([^}]+)\}").expect("couldn't compile regex");

    static ref NOT_STRING: &'static str = "configuration value is not a string";
    static ref NOT_INTEGER: &'static str = "configuration value is not an integer";
    static ref NOT_FLOAT: &'static str = "configuration value is not a floating-point value";
    static ref NOT_COMPLEX: &'static str = "configuration value is not a complex number value";
    static ref NOT_DATE: &'static str = "configuration value is not a date value";
    static ref NOT_DATETIME: &'static str = "configuration value is not a date/time value";
}

#[derive(Debug)]
pub(crate) enum DecoderError {
    InvalidBytes(Vec<u8>),
    Io(io::Error),
}

impl fmt::Display for DecoderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DecoderError::InvalidBytes(b) => write!(f, "invalid bytes: {:?}", b),
            DecoderError::Io(e) => write!(f, "I/O error: {:?}", e),
        }
    }
}

// no actual implementations needed, as defaults are in the trait itself
impl std::error::Error for DecoderError {}

#[derive(Debug)]
pub(crate) enum DecodeResult {
    EOF,
    Error(DecoderError),
    Char(char, Vec<u8>),
}

pub(crate) struct Decoder<'a> {
    reader: Box<dyn BufRead + 'a>,
    pub(crate) bytes_read: usize,
    log: bool,
}

impl<'a> Decoder<'a> {
    pub(crate) fn new<R: Read + 'a>(r: R) -> Self {
        let boxed = Box::new(r);
        let br = BufReader::new(boxed);

        Self {
            reader: Box::new(br),
            bytes_read: 0,
            log: false,
        }
    }

    pub(crate) fn decode(&mut self) -> DecodeResult {
        let mut pos: usize;
        let mut code_point: u32 = 0;
        let mut state = UTF8_ACCEPT;
        let mut the_bytes = vec![];

        loop {
            let reader = &mut self.reader;
            // we create a block just to get some bytes using fill_buf() and process some byes from
            // the buffer it gives us. Once we exit the block, we've given back the borrow and can
            // call consume().
            {
                let r = reader.fill_buf();
                let length: usize;
                let buf: &[u8];

                match r {
                    Ok(buffer) => {
                        buf = buffer;
                        length = buffer.len();
                        if self.log {
                            println!("Buffer is {} long", length);
                        }
                        if length == 0 {
                            return if state == UTF8_ACCEPT {
                                DecodeResult::EOF
                            } else {
                                DecodeResult::Error(DecoderError::InvalidBytes(the_bytes))
                            };
                        }
                        pos = 0;
                    }
                    Err(e) => {
                        return DecodeResult::Error(DecoderError::Io(e));
                    }
                }
                while pos < length {
                    let byte = buf[pos];
                    let kind: u32 = UTF8_LOOKUP[byte as usize] as u32;

                    the_bytes.push(byte);
                    code_point = if state != UTF8_ACCEPT {
                        (byte & 0x3F) as u32 | (code_point << 6)
                    } else {
                        (0xFF >> kind) & (byte as u32)
                    };
                    state = UTF8_LOOKUP[(256 + state + kind) as usize] as u32;
                    if self.log {
                        println!("byte = {}, kind = {}, state = {}", byte, kind, state);
                    }
                    if state == UTF8_REJECT {
                        break;
                    } else {
                        pos += 1;
                        if state == UTF8_ACCEPT {
                            break;
                        }
                    }
                }
            } // block which processes bytes in the buffer
            reader.consume(pos);
            self.bytes_read += pos;

            if state == UTF8_REJECT || state == UTF8_ACCEPT {
                break;
            }
        } // loop which processes until char or error
        if self.log {
            println!("exited loop, state = {}", state);
        }
        assert!(state == UTF8_REJECT || state == UTF8_ACCEPT);
        if state == UTF8_REJECT {
            DecodeResult::Error(DecoderError::InvalidBytes(the_bytes))
        } else {
            match std::char::from_u32(code_point) {
                Some(c) => DecodeResult::Char(c, the_bytes),
                None => DecodeResult::Error(DecoderError::InvalidBytes(the_bytes)),
            }
        }
    }
}

//
// Token and Tokenizer stuff
//
/// This represents a line and column location in CFG source.
#[derive(Debug, Copy, Clone, PartialEq, Hash, Eq, PartialOrd)]
pub struct Location {
    /// The line number of the location.
    pub line: u16,
    /// The column number of the location.
    pub column: u16,
}

impl Location {
    pub(crate) fn next_line(&mut self) {
        self.line += 1;
        self.column = 1;
    }

    pub(crate) fn update(&mut self, other: &Self) {
        *self = *other;
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.line, self.column)
    }
}

impl Ord for Location {
    fn cmp(&self, other: &Self) -> Ordering {
        let result = self.line.cmp(&other.column);

        if result != Ordering::Equal {
            return result;
        }
        self.column.cmp(&other.column)
    }
}

/// This represents the low-level errors which can occur when parsing CFG source. They all include
/// the source location where the error was detected.
#[derive(Debug, PartialEq)]
pub enum RecognizerError {
    /// This represents an I/O error (e.g. a network or disk read error).
    Io(Location),
    /// This represents an unexpected character at the start of a token.
    UnexpectedCharacter(char, Location),
    /// This represents a character which is invalid in the middle of a token.
    InvalidCharacter(char, Location),
    /// This represents an invalid number.
    InvalidNumber(Location),
    /// This represents an unterminated string. The start of the string is returned.
    UnterminatedString(Location),
    /// This represents where an invalid string was detected. An example would be a back-tick
    /// string containing a newline character.
    InvalidString(Location),
    /// This represents where a particular token was expected but not found. The text of the
    /// expected token, the text of the actual token and the location are returned.
    UnexpectedToken(String, String, Location),
    /// This represents where a value was expected but not found.
    ValueExpected(String, Location),
    /// This represents where an "atom" (identifier, number, string etc.) was expected but not found.
    AtomExpected(String, Location),
    /// This represents where a key (identifier or literal string) was expected but not found.
    KeyExpected(String, Location),
    /// This represents where a key/value separator was expected but not found.
    KeyValueSeparatorExpected(String, Location),
    /// This represents that a valid container (mapping or list) was expected, but not found.
    ContainerExpected(String, Location),
    /// This representsd an invalid escape sequence.
    InvalidEscapeSequence(usize, Location),
    /// This represents an unexpected list size. Currently, only one-dimensional lists are allowed.
    UnexpectedListSize(Location),
    /// This represents trailing text, e.g. at the end of an expression.
    TrailingText(Location),
}

/// This represents the kind of token. A deliberate choice was made to separate this from the
/// ScalarValue enumeration to keep the token kind as just a simple enumeration, as in other
/// language implementations.
#[derive(Debug, Copy, Clone, PartialEq, Hash, Eq)]
pub enum TokenKind {
    /// This represents the token at the end of the input stream.
    EOF = 0,
    /// This represents a word (identifier).
    Word,
    /// This represents a literal number.
    Number,
    /// This represents a literal string.
    String,
    /// This represents the "\n" punctuation character.
    Newline,
    /// This represents the "{" punctuation character.
    LeftCurly,
    /// This represents the "}" punctuation character.
    RightCurly,
    /// This represents the "[" punctuation character.
    LeftBracket,
    /// This represents the "]" punctuation character.
    RightBracket,
    /// This represents the "(>)" punctuation character.
    LeftParenthesis,
    /// This represents the ")" punctuation character.
    RightParenthesis,
    /// This represents the "<>>" punctuation character.
    LessThan,
    /// This represents the ">" punctuation character.
    GreaterThan,
    /// This represents the "<=>" punctuation sequence.
    LessThanOrEqual,
    /// This represents the ">=" punctuation sequence.
    GreaterThanOrEqual,
    /// This represents the "=" punctuation character.
    Assign,
    /// This represents the "==" punctuation sequence.
    Equal,
    /// This represents the "!=" punctuation sequence.
    Unequal,
    /// This represents the "<>>>" punctuation sequence.
    AltUnequal,
    /// This represents the "<<>>>>" punctuation sequence.
    LeftShift,
    /// This represents the ">>" punctuation sequence.
    RightShift,
    /// This represents the "." punctuation character.
    Dot,
    /// This represents the "," punctuation character.
    Comma,
    /// This represents the ":" punctuation character.
    Colon,
    /// This represents the "@" punctuation character.
    At,
    /// This represents the "+" punctuation character.
    Plus,
    /// This represents the "-" punctuation character.
    Minus,
    /// This represents the "*" punctuation character.
    Star,
    /// This represents the "**" punctuation sequence.
    Power,
    /// This represents the "/" punctuation character.
    Slash,
    /// This represents the "//" punctuation sequence.
    SlashSlash,
    /// This represents the "%" punctuation character.
    Modulo,
    /// This represents the "`" punctuation character.
    BackTick,
    /// This represents the "$" punctuation character.
    Dollar,
    /// This represents the "true" keyword.
    True,
    /// This represents the "false" keyword.
    False,
    /// This represents the "null" keyword.
    None,
    /// This represents an equivalence - the "is" operator.
    Is,
    /// This represents a containment - the "in" operator.
    In,
    /// This represents a logical negation - the ! or "not" operator.
    Not,
    /// This represents a logical and - the && or "and" operator.
    And,
    /// This represents a logical or - the || or "or" operator.
    Or,
    /// This represents a bitwise and - the & operator.
    BitwiseAnd,
    /// This represents a bitwise or - the | operator.
    BitwiseOr,
    /// This represents a bitwise exclusive or - the ^ operator.
    BitwiseXor,
    /// This represents a bitwise complement - the ~ operator.
    BitwiseComplement,
    /// This represents a complex value.
    Complex,
    /// This represents the "is not" operator.
    IsNot,
    /// This represents the "not in" operator.
    NotIn,
}

/// This represents a scalar value corresponding to a token.
#[derive(Debug, Clone, PartialEq)]
pub enum ScalarValue {
    /// This is the (absence of) value for punctuation tokens.
    None,
    // Above: absence of a value (e.g. punctuation tokens). Note that we could remove this and use
    // Option<ScalarValue>, but this just leads to a lot of unwrap() and Some(xxx) all over
    // the place, which hurts readability.
    /// This is the value for the "null" keyword.
    Null,
    /// This is the value for the "true" and "false" keywords.
    Bool(bool),
    /// This is the value for an identifier.
    Identifier(String),
    /// This is the value for a string literal.
    String(String),
    /// This is the value for an integer.
    Integer(i64),
    /// This is the value for a floating-point number.
    Float(f64),
    /// This is the value for a complex number.
    Complex(Complex64),
    /// This is the value for a date.
    Date(NaiveDate),
    /// This is the value for a date/time.
    DateTime(DateTime<FixedOffset>),
}

impl fmt::Display for ScalarValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScalarValue::None => write!(f, "<None>"),
            ScalarValue::Bool(b) => write!(f, "{}", b),
            ScalarValue::Null => write!(f, "null"),
            ScalarValue::Integer(i) => write!(f, "{}", i),
            ScalarValue::Identifier(s) => write!(f, "{}", s),
            ScalarValue::String(s) => write!(f, "{}", s),
            ScalarValue::Float(fv) => write!(f, "{}", fv),
            ScalarValue::Complex(c) => {
                if c.re != 0f64 && c.im != 0f64 {
                    write!(f, "{} + {}j", c.re, c.im)
                } else if c.re == 0f64 {
                    write!(f, "{}j", c.im)
                } else {
                    write!(f, "{}", c.re)
                }
            }
            ScalarValue::Date(d) => write!(f, "Date<{}>", d),
            ScalarValue::DateTime(dt) => write!(f, "DateTime<{}>", dt),
        }
    }
}

/// This represents a lexical token in CFG source.
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    /// This is the kind of token.
    pub kind: TokenKind,
    /// This is the text of the token.
    pub text: String,
    /// This is the value of the token.
    pub value: ScalarValue,
    /// This is the location of the start of the token.
    pub start: Location,
    /// This is the location of the end of the token.
    pub end: Location,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Token[{}, {}]({:?}:{}:{})",
            self.start.line, self.start.column, self.kind, self.text, self.value
        )
    }
}

/// This represents a unary node, typically used in expressions such as -A.
#[derive(Debug, Clone, PartialEq)]
pub struct UnaryNode {
    /// This is the kind of node, i.e. the operator.
    pub(crate) kind: TokenKind,
    /// This is the operand.
    pub(crate) operand: Box<ASTValue>,
    /// This is the location of the node, usually that of the operator.
    pub start: Location,
}

impl fmt::Display for UnaryNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "UnaryNode[{}, {}]({:?}, {})",
            self.start.line, self.start.column, self.kind, self.operand
        )
    }
}

/// This represents a binary node, typically used in expressions such as A + B.
#[derive(Debug, Clone, PartialEq)]
pub struct BinaryNode {
    /// This is the kind of node, i.e. the operator.
    pub(crate) kind: TokenKind,
    /// This is the left-hand side of the binary.
    pub(crate) left: Box<ASTValue>,
    /// This is the right-hand side of the binary.
    pub(crate) right: Box<ASTValue>,
    /// This is the location of the node, usually that of the operator.
    pub start: Location,
}

impl fmt::Display for BinaryNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "BinaryNode[{}, {}]({:?}, {}, {})",
            self.start.line, self.start.column, self.kind, self.left, self.right
        )
    }
}

/// This represents AST nodes corresponding to fragments of CFG source.
#[derive(Debug, Clone, PartialEq)]
pub enum ASTValue {
    /// This is a token in the CFG grammar.
    TokenValue(Token),
    /// This is a unary node.
    Unary(UnaryNode),
    /// This is a binary node.
    Binary(BinaryNode),
    /// This is a list node.
    List(Vec<ASTValue>),
    /// This is a mapping node.
    Mapping(Vec<(Token, ASTValue)>),
    /// This is a slice node. It's produced when parsing slices.
    Slice(
        Location,
        Box<Option<ASTValue>>,
        Box<Option<ASTValue>>,
        Box<Option<ASTValue>>,
    ),
}

impl fmt::Display for ASTValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ASTValue::TokenValue(t) => write!(f, "{}", t),
            ASTValue::Unary(u) => write!(f, "{}", u),
            ASTValue::Binary(b) => write!(f, "{}", b),
            ASTValue::List(lv) => {
                let mut s = "[".to_string();
                for e in lv {
                    write!(s, "{}", e).unwrap();
                    write!(s, ", ").unwrap();
                }
                // remove last ", "
                s.pop();
                s.pop();
                write!(s, "]").unwrap();
                write!(f, "{}", s)
            }
            ASTValue::Mapping(mv) => {
                let mut s = "{".to_string();
                for e in mv {
                    write!(s, "{}", e.0).unwrap();
                    write!(s, ":").unwrap();
                    write!(s, "{}", e.1).unwrap();
                    write!(s, ", ").unwrap();
                }
                // remove last ", "
                s.pop();
                s.pop();
                write!(s, "}}").unwrap();
                write!(f, "{}", s)
            }
            ASTValue::Slice(loc, start, stop, step) => {
                write!(f, "Slice[{}, {}](", loc.line, loc.column).unwrap();
                match &**start {
                    None => write!(f, "None").unwrap(),
                    Some(v) => write!(f, "{}", v).unwrap(),
                };
                write!(f, ", ").unwrap();
                match &**stop {
                    None => write!(f, "None").unwrap(),
                    Some(v) => write!(f, "{}", v).unwrap(),
                };
                write!(f, ", ").unwrap();
                match &**step {
                    None => write!(f, "None").unwrap(),
                    Some(v) => write!(f, "{}", v).unwrap(),
                };
                write!(f, ")")
                // write!(f, "Slice({}, {:?}, {:?}, {:?})", loc, start, stop, step)
            }
        }
    }
}

struct PushBackInfo {
    pub(crate) c: char,
    pub(crate) location: Location,
}

pub(crate) struct Tokenizer<'a> {
    reader: Decoder<'a>,
    char_location: Location,
    location: Location,
    pushed_back: Vec<PushBackInfo>,
    log: bool,
}

macro_rules! get_char {
    ($self: expr) => {{
        let r = $self.get_char();

        match r {
            Err(_) => {
                return Err(RecognizerError::Io($self.char_location.clone()));
            }
            Ok(c) => c,
        }
    }};
}

macro_rules! append_char {
    ($self: expr, $text: expr, $c: expr, $endloc: expr) => {{
        $text.push($c);
        $endloc.update(&$self.char_location);
    }};
}

pub(crate) fn is_identifier(s: &str) -> bool {
    IDENTIFIER_PATTERN.is_match(s)
}

fn find_in_slice(text: &[char], c: char) -> isize {
    let mut result = -1;

    for (i, ch) in text.iter().enumerate() {
        if *ch == c {
            result = i as isize;
            break;
        }
    }
    result
}

macro_rules! loc {
    ($line:expr, $column:expr) => {{
        Location {
            line: $line,
            column: $column,
        }
    }};
}

impl<'a> Tokenizer<'a> {
    pub(crate) fn new(r: Box<dyn Read + 'a>) -> Self {
        let br = BufReader::new(r);
        let b = Box::new(br);
        Self {
            reader: Decoder::new(b),
            char_location: loc!(1, 1),
            location: loc!(1, 1),
            pushed_back: vec![],
            log: false,
        }
    }

    pub(crate) fn push_back(&mut self, c: char) {
        let push_back_info = PushBackInfo {
            c,
            location: self.char_location,
        };
        self.pushed_back.push(push_back_info);
    }

    pub(crate) fn get_char(&mut self) -> Result<Option<char>> {
        let result;

        if let Some(push_back_info) = self.pushed_back.pop() {
            result = Ok(Some(push_back_info.c));
            self.char_location.update(&push_back_info.location);
            self.location.update(&push_back_info.location); // will be bumped later
        } else {
            self.char_location.update(&self.location);
            match self.reader.decode() {
                DecodeResult::Char(c, _) => {
                    result = Ok(Some(c));
                }
                DecodeResult::EOF => {
                    result = Ok(Option::None);
                }
                DecodeResult::Error(e) => match e {
                    DecoderError::Io(e) => result = Err(e),
                    e => {
                        result = Err(Error::new(ErrorKind::InvalidData, e));
                    }
                },
            }
        }
        if let Ok(v) = &result {
            if let Some(c) = v {
                self.location.column += 1;
                if *c == '\n' {
                    self.location.next_line();
                }
            }
        }
        result
    }

    fn get_number(
        &mut self,
        text: &mut Vec<char>,
        start_location: Location,
        end_location: &mut Location,
    ) -> StdResult<(TokenKind, ScalarValue), RecognizerError> {
        let mut kind = TokenKind::Number;
        let mut value = ScalarValue::None;
        let mut in_exponent = false;
        let mut radix = 0;
        let mut dot_seen = text.contains(&'.');
        let mut last_was_digit = match text.last() {
            None => false,
            Some(c) => c.is_ascii_hexdigit(),
        };
        let mut fail_location: Option<Location> = Option::None;
        let mut lastc;

        fn ends_with(text: &[char], c: char) -> bool {
            match text.last() {
                None => false,
                Some(ch) => *ch == c,
            }
        }

        loop {
            let c = get_char!(self);

            lastc = c;
            match c {
                None => break,
                Some(ch) => {
                    if ch == '.' {
                        dot_seen = true;
                    }
                    if ch == '_' {
                        if last_was_digit {
                            append_char!(self, text, ch, end_location);
                            last_was_digit = false;
                            continue;
                        }
                        fail_location = Some(self.char_location);
                    }
                    last_was_digit = false; // unless set in one of the clauses below
                    if ((radix == 0) && (ch >= '0') && (ch <= '9'))
                        || ((radix == 2) && (ch >= '0') && (ch <= '1'))
                        || ((radix == 8) && (ch >= '0') && (ch <= '7'))
                        || ((radix == 16) && ch.is_ascii_hexdigit())
                    {
                        append_char!(self, text, ch, end_location);
                        last_was_digit = true;
                    } else if ((ch == 'o')
                        || (ch == 'O')
                        || (ch == 'x')
                        || (ch == 'X')
                        || (ch == 'b')
                        || (ch == 'B'))
                        && (text.len() == 1)
                        && (text[0] == '0')
                    {
                        if (ch == 'o') || (ch == 'O') {
                            radix = 8;
                        } else if (ch == 'x') || (ch == 'X') {
                            radix = 16;
                        } else {
                            radix = 2;
                        }
                        append_char!(self, text, ch, end_location);
                    } else if (radix == 0) && (ch == '.') && !in_exponent && !text.contains(&ch) {
                        append_char!(self, text, ch, end_location);
                    } else if (radix == 0)
                        && (ch == '-')
                        && !text[1..].contains(&'-')
                        && in_exponent
                    {
                        append_char!(self, text, ch, end_location);
                    } else if (radix == 0)
                        && ((ch == 'e') || (ch == 'E'))
                        && !text.contains(&'e')
                        && !text.contains(&'E')
                    {
                        if ends_with(text, '_') {
                            fail_location = Some(self.char_location);
                            break;
                        } else {
                            append_char!(self, text, ch, end_location);
                            in_exponent = true;
                        }
                    } else {
                        break;
                    }
                }
            }
        }
        if ends_with(text, '_') {
            if fail_location.is_none() {
                let mut loc = self.char_location;

                loc.column -= 1;
                fail_location = Some(loc);
            }
        } else {
            match lastc {
                None => {}
                Some(ch) => {
                    if (radix == 0) && ((ch == 'j') || (ch == 'J')) {
                        append_char!(self, text, ch, end_location);
                        kind = TokenKind::Complex;
                    } else {
                        // not allowed to have a letter or digit which wasn't accepted
                        if (ch != '.') && !ch.is_alphanumeric() {
                            self.push_back(ch);
                        } else {
                            fail_location = Some(self.char_location);
                        }
                    }
                }
            }
        }
        if fail_location.is_none() {
            let s = text.iter().cloned().collect::<String>().replace("_", "");
            if radix != 0 {
                match i64::from_str_radix(&s[2..], radix) {
                    Ok(v) => value = ScalarValue::Integer(v),
                    Err(_) => fail_location = Some(start_location),
                }
            } else if kind == TokenKind::Complex {
                match s[..s.len() - 1].parse::<f64>() {
                    Ok(v) => value = ScalarValue::Complex(Complex64::new(0.0, v)),
                    Err(_) => fail_location = Some(start_location),
                }
            } else if in_exponent || dot_seen {
                match s.parse::<f64>() {
                    Ok(v) => value = ScalarValue::Float(v),
                    Err(_) => fail_location = Some(start_location),
                }
            } else {
                radix = if text[0] == '0' { 8 } else { 10 };
                match i64::from_str_radix(&s, radix) {
                    Ok(v) => value = ScalarValue::Integer(v),
                    Err(_) => fail_location = Some(start_location),
                }
            }
        }
        match fail_location {
            Some(loc) => Err(RecognizerError::InvalidNumber(loc)),
            None => Ok((kind, value)),
        }
    }

    fn parse_escapes(
        &self,
        mut text: &[char],
        loc: Location,
    ) -> StdResult<String, RecognizerError> {
        let result;
        let mut i = find_in_slice(text, '\\');

        if i < 0 {
            result = text.iter().cloned().collect::<String>();
        } else {
            let mut out: Vec<char> = vec![];
            let mut failed = false;

            while i >= 0 {
                let n = text.len();
                let mut u = i as usize;

                if i > 0 {
                    out.extend_from_slice(&text[..u]);
                }
                let c = text[i as usize + 1];
                if ESCAPES.contains_key(&c) {
                    out.push(ESCAPES[&c]);
                    u += 2;
                } else if c == 'x' || c == 'X' || c == 'u' || c == 'U' {
                    let slen = if c == 'x' || c == 'X' {
                        4
                    } else if c == 'u' {
                        6
                    } else {
                        10
                    };

                    if u + slen > n {
                        failed = true;
                        break;
                    }
                    let p = text[u + 2..u + slen].iter().cloned().collect::<String>();
                    match u32::from_str_radix(&p, 16) {
                        Ok(v) => match std::char::from_u32(v) {
                            Some(c) => {
                                out.push(c);
                                u += slen;
                            }
                            None => {
                                failed = true;
                                break;
                            }
                        },
                        Err(_) => {
                            failed = true;
                            break;
                        }
                    }
                } else {
                    failed = true;
                    break;
                }
                text = &text[u..];
                i = find_in_slice(text, '\\');
            }
            if failed {
                return Err(RecognizerError::InvalidEscapeSequence(i as usize, loc));
            }
            out.extend(text);
            result = out.iter().cloned().collect::<String>();
        }
        Ok(result)
    }

    pub(crate) fn get_token(&mut self) -> StdResult<Token, RecognizerError> {
        let mut kind;
        let mut value = ScalarValue::None;
        let mut text: Vec<char> = vec![];
        let mut start_location = loc!(1, 1);
        let mut end_location = loc!(1, 1);
        let mut s = String::new();

        loop {
            let mut c = get_char!(self);

            start_location.update(&self.char_location);
            // This value will be overridden for Newline below, but is
            // generally the right value
            end_location.update(&self.char_location);

            match c {
                None => {
                    kind = TokenKind::EOF;
                    break;
                }
                Some('#') => {
                    text.push('#');
                    kind = TokenKind::Newline;
                    loop {
                        let ch = get_char!(self);
                        match ch {
                            None => break,
                            Some(c) => {
                                text.push(c);
                                if c == '\n' {
                                    break;
                                }
                            }
                        }
                    }
                    //                    self.location.next_line();
                    end_location.update(&self.location);
                    break;
                }
                Some('\n') => {
                    append_char!(self, text, '\n', end_location);
                    kind = TokenKind::Newline;
                    end_location.update(&self.location);
                    end_location.column -= 1;
                    break;
                }
                Some('\r') => {
                    let nc = get_char!(self);

                    match nc {
                        None => {}
                        Some('\n') => {}
                        Some(c) => self.push_back(c),
                    }
                    kind = TokenKind::Newline;
                    end_location.update(&self.location);
                    end_location.column -= 1;
                    break;
                }
                Some('\\') => {
                    let nc = get_char!(self);

                    match nc {
                        None => {}
                        Some('\n') => {
                            end_location.update(&self.location);
                            continue;
                        }
                        Some('\r') => {
                            let nnc = get_char!(self);

                            match nnc {
                                None => {}
                                Some('\n') => {
                                    end_location.update(&self.location);
                                    continue;
                                }
                                Some(c) => {
                                    return Err(RecognizerError::UnexpectedCharacter(
                                        c,
                                        self.char_location,
                                    ));
                                }
                            }
                        }
                        Some(c) => {
                            return Err(RecognizerError::UnexpectedCharacter(
                                c,
                                self.char_location,
                            ));
                        }
                    }
                }
                Some(ch) if ch.is_whitespace() => continue,
                Some(ch) if ch.is_alphabetic() || ch == '_' => {
                    kind = TokenKind::Word;

                    append_char!(self, text, ch, end_location);
                    loop {
                        c = get_char!(self);
                        match c {
                            None => break,
                            Some(c) if c.is_alphanumeric() || c == '_' => {
                                append_char!(self, text, c, end_location)
                            }
                            Some(c) => {
                                self.push_back(c);
                                break;
                            }
                        }
                    }
                    s = text.iter().cloned().collect::<String>();
                    if self.log {
                        println!("word: {}", s);
                    }
                    if !KEYWORDS.contains_key(&s) {
                        value = ScalarValue::Identifier(s.clone());
                    } else {
                        kind = KEYWORDS[&s];
                        if KEYWORD_VALUES.contains_key(&s) {
                            value = KEYWORD_VALUES[&s].clone();
                        }
                    }
                    break;
                }
                Some('`') => {
                    let mut unterminated = false;

                    kind = TokenKind::BackTick;
                    append_char!(self, text, '`', end_location);
                    loop {
                        let c = get_char!(self);

                        match c {
                            None => {
                                unterminated = true;
                                break;
                            }
                            Some(ch) if !ch.is_control() => {
                                append_char!(self, text, ch, end_location);
                                if ch == '`' {
                                    break;
                                }
                            }
                            Some(_ch) => {
                                return Err(RecognizerError::InvalidString(self.char_location));
                            }
                        }
                    }
                    if self.char_location.column > 1 {
                        self.char_location.column -= 1;
                    }
                    if unterminated {
                        return Err(RecognizerError::UnterminatedString(self.char_location));
                    }
                    value = ScalarValue::String(
                        self.parse_escapes(&text[1..text.len() - 1], start_location)?,
                    );
                    break;
                }
                Some(ch) if ch == '\'' || ch == '"' => {
                    kind = TokenKind::String;

                    let quote = ch;
                    let mut multi_line = false;
                    let mut escaped = false;
                    let mut unterminated = false;

                    append_char!(self, text, ch, end_location);
                    let c1 = get_char!(self);
                    let c1_loc = self.char_location;

                    match c1 {
                        None => unterminated = true,
                        Some(ch1) => {
                            if ch1 != quote {
                                self.push_back(ch1);
                            } else {
                                let c2 = get_char!(self);

                                match c2 {
                                    Some(ch2) => {
                                        if ch2 != quote {
                                            self.push_back(ch2);
                                            self.push_back(ch1);
                                        } else {
                                            multi_line = true;
                                            text.push(quote);
                                            append_char!(self, text, quote, end_location);
                                        }
                                    }
                                    None => {
                                        self.char_location.update(&c1_loc);
                                        self.push_back(ch1);
                                    }
                                }
                            }
                        }
                    }
                    if self.char_location.column > 1 {
                        self.char_location.column -= 1;
                    }
                    if unterminated {
                        return Err(RecognizerError::UnterminatedString(self.char_location));
                    }
                    let quoter_len = text.len();
                    loop {
                        let c = get_char!(self);

                        match c {
                            None => {
                                unterminated = true;
                                break;
                            }
                            Some(ch) => {
                                append_char!(self, text, ch, end_location);
                                if ch == quote && !escaped {
                                    let n = text.len();
                                    if !multi_line
                                        || (n >= 6)
                                            && (text[n - 3..n] == text[..3])
                                            && text[n - 4] != '\\'
                                    {
                                        break;
                                    }
                                }
                                escaped = if ch == '\\' { !escaped } else { false };
                            }
                        }
                    }
                    if self.char_location.column > 1 {
                        self.char_location.column -= 1;
                    }
                    if unterminated {
                        return Err(RecognizerError::UnterminatedString(self.char_location));
                    }
                    value = ScalarValue::String(self.parse_escapes(
                        &text[quoter_len..text.len() - quoter_len],
                        start_location,
                    )?);
                    break;
                }
                Some(ch) if ch.is_numeric() => {
                    append_char!(self, text, ch, end_location);
                    // sadly, can't use direct destructuring (kind, value) = ...
                    let (k, v) = self.get_number(&mut text, start_location, &mut end_location)?;
                    kind = k;
                    value = v;
                    break;
                }
                Some('=') => {
                    let nc = get_char!(self);

                    match nc {
                        Some('=') => {
                            kind = TokenKind::Equal;
                            text.push('=');
                            append_char!(self, text, '=', end_location);
                            break;
                        }
                        Some(nch) => {
                            kind = TokenKind::Assign;
                            append_char!(self, text, '=', end_location);
                            self.push_back(nch);
                            break;
                        }
                        None => {
                            kind = TokenKind::Assign;
                            append_char!(self, text, '=', end_location);
                            break;
                        }
                    }
                }
                Some(ch) if PUNCTUATION.contains_key(&ch) => {
                    kind = PUNCTUATION[&ch];
                    append_char!(self, text, ch, end_location);
                    match ch {
                        '-' => {
                            let nc = get_char!(self);
                            match nc {
                                None => break,
                                Some(nch) if nch.is_numeric() || (nch == '.') => {
                                    append_char!(self, text, nch, end_location);
                                    // sadly, can't use direct destructuring (kind, value) = ...
                                    let (k, v) = self.get_number(
                                        &mut text,
                                        start_location,
                                        &mut end_location,
                                    )?;
                                    kind = k;
                                    value = v;
                                }
                                Some(nch) => self.push_back(nch),
                            }
                        }
                        '.' => {
                            let nc = get_char!(self);

                            match nc {
                                None => break,
                                Some(nch) if nch.is_numeric() => {
                                    append_char!(self, text, nch, end_location);
                                    // sadly, can't use direct destructuring (kind, value) = ...
                                    let (k, v) = self.get_number(
                                        &mut text,
                                        start_location,
                                        &mut end_location,
                                    )?;
                                    kind = k;
                                    value = v;
                                }
                                Some(nch) => self.push_back(nch),
                            }
                        }
                        '<' => {
                            let nc = get_char!(self);

                            match nc {
                                None => {}
                                Some(nch) => {
                                    if "=<>".contains(nch) {
                                        append_char!(self, text, nch, end_location);
                                    }
                                    match nch {
                                        '=' => kind = TokenKind::LessThanOrEqual,
                                        '<' => kind = TokenKind::LeftShift,
                                        '>' => kind = TokenKind::AltUnequal,
                                        _ => self.push_back(nch),
                                    }
                                }
                            }
                            break;
                        }
                        '>' => {
                            let nc = get_char!(self);

                            match nc {
                                None => {}
                                Some(nch) => {
                                    if "=>".contains(nch) {
                                        append_char!(self, text, nch, end_location);
                                    }
                                    match nch {
                                        '=' => kind = TokenKind::GreaterThanOrEqual,
                                        '>' => kind = TokenKind::RightShift,
                                        _ => self.push_back(nch),
                                    }
                                }
                            }
                            break;
                        }
                        '!' => {
                            let nc = get_char!(self);

                            match nc {
                                None => {}
                                Some(nch) => match nch {
                                    '=' => {
                                        append_char!(self, text, nch, end_location);
                                        kind = TokenKind::Unequal;
                                    }
                                    _ => self.push_back(nch),
                                },
                            }
                            break;
                        }
                        '*' => {
                            let nc = get_char!(self);

                            match nc {
                                None => {}
                                Some(nch) => match nch {
                                    '*' => {
                                        append_char!(self, text, nch, end_location);
                                        kind = TokenKind::Power;
                                    }
                                    _ => self.push_back(nch),
                                },
                            }
                            break;
                        }
                        '/' => {
                            let nc = get_char!(self);

                            match nc {
                                None => {}
                                Some(nch) => match nch {
                                    '/' => {
                                        append_char!(self, text, nch, end_location);
                                        kind = TokenKind::SlashSlash;
                                    }
                                    _ => self.push_back(nch),
                                },
                            }
                            break;
                        }
                        '&' | '|' => {
                            let nc = get_char!(self);

                            match nc {
                                None => {}
                                Some(nch) => {
                                    if nch == ch {
                                        append_char!(self, text, nch, end_location);
                                        kind = if ch == '&' {
                                            TokenKind::And
                                        } else {
                                            TokenKind::Or
                                        }
                                    }
                                }
                            }
                            break;
                        }
                        _ => {}
                    }
                    break;
                }
                Some(ch) => {
                    return Err(RecognizerError::UnexpectedCharacter(ch, self.char_location));
                }
            }
        }
        if self.log {
            println!("{}, {}, {:?}", kind as i32, s, value);
        }
        if s.is_empty() {
            s = text.iter().cloned().collect::<String>();
        }
        Ok(Token {
            kind,
            text: s,
            value,
            start: start_location,
            end: end_location,
        })
    }
}

/// This implements the low-level parser of CFG source text.
pub struct Parser<'a> {
    tokenizer: Tokenizer<'a>,
    next_token: Token,
}

pub(crate) fn token_text(k: TokenKind) -> String {
    TOKEN_TEXT[&k].clone()
}

impl<'a> Parser<'a> {
    /// Return a new instance of the parser using the provided reader for the source text. The
    /// first token is read.
    pub fn new(r: Box<dyn Read + 'a>) -> StdResult<Self, RecognizerError> {
        let mut tokenizer = Tokenizer::new(r);
        let t = tokenizer.get_token();
        match t {
            Err(e) => Err(e),
            Ok(token) => Ok(Self {
                tokenizer,
                next_token: token,
            }),
        }
    }

    /// Return `true` if the parser has reached the end of the source, else `false`.
    pub fn at_end(&self) -> bool {
        self.next_token.kind == TokenKind::EOF
    }

    /// Return the current location of the parser in the source.
    pub fn location(&self) -> Location {
        self.next_token.start
    }

    fn advance(&mut self) -> StdResult<TokenKind, RecognizerError> {
        let r = self.tokenizer.get_token();

        match r {
            Err(e) => Err(e),
            Ok(token) => {
                let k = token.kind;

                self.next_token = token;
                Ok(k)
            }
        }
    }

    fn expect(&mut self, kind: TokenKind) -> StdResult<Token, RecognizerError> {
        if self.next_token.kind != kind {
            Err(RecognizerError::UnexpectedToken(
                token_text(kind),
                token_text(self.next_token.kind),
                self.next_token.start,
            ))
        } else {
            let curr = self.next_token.clone();
            let r = self.advance();

            match r {
                Err(e) => Err(e),
                Ok(_) => Ok(curr),
            }
        }
    }

    pub(crate) fn consume_new_lines(&mut self) -> StdResult<TokenKind, RecognizerError> {
        let mut result = self.next_token.kind;

        while result == TokenKind::Newline {
            result = self.advance()?;
        }
        Ok(result)
    }

    pub(crate) fn strings(&mut self) -> StdResult<Token, RecognizerError> {
        let mut result = self.next_token.clone();
        let k = self.advance()?;

        if k == TokenKind::String {
            let mut all_text: Vec<char> = vec![];
            let start = result.start;
            let mut end = self.next_token.end;

            match &result.value {
                ScalarValue::String(s) => all_text.extend(s.chars()),
                e => panic!("string value expected, but found {:?}", e),
            }
            loop {
                match &self.next_token.value {
                    ScalarValue::String(s) => all_text.extend(s.chars()),
                    e => panic!("string value expected, but found {:?}", e),
                }
                let k = self.advance()?;
                if k == TokenKind::String {
                    end = self.next_token.end;
                } else {
                    break;
                }
            }
            // now construct the result
            let s = all_text.iter().collect::<String>();
            result = Token {
                kind: result.kind,
                text: s.clone(),
                value: ScalarValue::String(s),
                start,
                end,
            }
        }
        Ok(result)
    }

    pub(crate) fn value(&mut self) -> StdResult<Token, RecognizerError> {
        let kind = self.next_token.kind;

        if !VALUE_STARTERS.contains(&kind) {
            Err(RecognizerError::ValueExpected(
                token_text(kind),
                self.next_token.start,
            ))
        } else {
            let t;

            if kind == TokenKind::String {
                t = self.strings();
            } else {
                t = Ok(self.next_token.clone());
                self.advance()?;
            }
            t
        }
    }

    pub(crate) fn atom(&mut self) -> StdResult<ASTValue, RecognizerError> {
        let kind = self.next_token.kind;

        match kind {
            TokenKind::LeftCurly => self.mapping(),
            TokenKind::LeftBracket => self.list(),
            TokenKind::LeftParenthesis => match self.expect(TokenKind::LeftParenthesis) {
                Err(e) => Err(e),
                Ok(_) => {
                    let result = self.expr();

                    match self.expect(TokenKind::RightParenthesis) {
                        Err(e) => Err(e),
                        _ => result,
                    }
                }
            },
            TokenKind::Dollar => {
                let spos = self.next_token.start;
                match self.advance() {
                    Err(e) => Err(e),
                    Ok(_) => match self.expect(TokenKind::LeftCurly) {
                        Err(e) => Err(e),
                        Ok(_) => match self.primary() {
                            Err(e) => Err(e),
                            Ok(v) => match self.expect(TokenKind::RightCurly) {
                                Err(e) => Err(e),
                                _ => Ok(ASTValue::Unary(UnaryNode {
                                    kind,
                                    operand: Box::new(v),
                                    start: spos,
                                })),
                            },
                        },
                    },
                }
            }
            v => {
                if VALUE_STARTERS.contains(&v) {
                    match self.value() {
                        Err(e) => Err(e),
                        Ok(v) => Ok(ASTValue::TokenValue(v)),
                    }
                } else {
                    Err(RecognizerError::AtomExpected(
                        token_text(v),
                        self.next_token.start,
                    ))
                }
            }
        }
    }

    fn list_element(&mut self) -> StdResult<ASTValue, RecognizerError> {
        let loc = self.next_token.start;
        let result;
        let v = self.list_body()?;

        match v {
            ASTValue::List(lv) => {
                let n = lv.len();

                if n != 1 {
                    return Err(RecognizerError::UnexpectedListSize(loc));
                }
                result = lv[0].clone();
            }
            _ => {
                panic!("unexpected when parsing list: {:?}", v);
            }
        }
        Ok(result)
    }

    pub(crate) fn trailer(&mut self) -> StdResult<(TokenKind, ASTValue), RecognizerError> {
        let mut kind = self.next_token.kind;
        let result;

        if kind != TokenKind::LeftBracket {
            self.expect(TokenKind::Dot)?;
            result = ASTValue::TokenValue(self.expect(TokenKind::Word)?);
        } else {
            kind = self.advance()?;

            let spos = self.next_token.start;
            let is_slice;
            let mut start: Option<ASTValue> = None;

            if kind == TokenKind::Colon {
                // it's a slice like [:xyz:abc]
                is_slice = true;
            } else {
                start = Some(self.list_element()?);
                is_slice = self.next_token.kind == TokenKind::Colon;
            }
            if !is_slice {
                kind = TokenKind::LeftBracket;
                result = start.unwrap();
            } else {
                let mut stop: Option<ASTValue> = None;
                let mut step: Option<ASTValue> = None;
                let mut tk = self.advance()?;

                if tk == TokenKind::Colon {
                    // no stop, but there might be a step
                    tk = self.advance()?;
                    if tk != TokenKind::RightBracket {
                        step = Some(self.list_element()?);
                    }
                } else if tk != TokenKind::RightBracket {
                    stop = Some(self.list_element()?);
                    if self.next_token.kind == TokenKind::Colon {
                        let tk = self.advance()?;

                        if tk != TokenKind::RightBracket {
                            step = Some(self.list_element()?);
                        }
                    }
                }
                kind = TokenKind::Colon;
                result = ASTValue::Slice(spos, Box::new(start), Box::new(stop), Box::new(step));
            }
            self.expect(TokenKind::RightBracket)?;
        }
        Ok((kind, result))
    }

    pub(crate) fn primary(&mut self) -> StdResult<ASTValue, RecognizerError> {
        let mut result = self.atom();

        if result.is_err() {
            return result;
        }
        let mut kind = self.next_token.kind;

        while kind == TokenKind::Dot || kind == TokenKind::LeftBracket {
            let rhs;
            let spos = self.next_token.start;
            let (k, r) = self.trailer()?;

            kind = k;
            rhs = r;
            result = Ok(ASTValue::Binary(BinaryNode {
                kind,
                left: Box::new(result.expect("a valid LHS was expected")),
                right: Box::new(rhs),
                start: spos,
            }));
            kind = self.next_token.kind;
        }
        result
    }

    pub(crate) fn list_body(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.consume_new_lines() {
            Err(e) => Err(e),
            Ok(mut k) => {
                let mut result = vec![];

                while EXPRESSION_STARTERS.contains(&k) {
                    result.push(self.expr()?);
                    k = self.next_token.kind;
                    if k != TokenKind::Newline && k != TokenKind::Comma {
                        break;
                    }
                    self.advance()?;
                    k = self.consume_new_lines()?;
                }
                Ok(ASTValue::List(result))
            }
        }
    }

    pub(crate) fn list(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.expect(TokenKind::LeftBracket) {
            Err(e) => Err(e),
            Ok(_) => match self.list_body() {
                Err(e) => Err(e),
                Ok(lb) => match self.expect(TokenKind::RightBracket) {
                    Err(e) => Err(e),
                    Ok(_) => Ok(lb),
                },
            },
        }
    }

    pub(crate) fn object_key(&mut self) -> StdResult<Token, RecognizerError> {
        let result;

        if self.next_token.kind == TokenKind::String {
            self.strings()
        } else {
            result = Ok(self.next_token.clone());
            match self.advance() {
                Err(e) => Err(e),
                Ok(_) => result,
            }
        }
    }

    pub(crate) fn mapping_body(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.consume_new_lines() {
            Err(e) => Err(e),
            Ok(mut k) => {
                if k == TokenKind::RightCurly || k == TokenKind::EOF {
                    // for example, an empty {} or an empty file.
                    Ok(ASTValue::Mapping(vec![]))
                } else if k != TokenKind::Word && k != TokenKind::String {
                    Err(RecognizerError::KeyExpected(
                        token_text(k),
                        self.next_token.start,
                    ))
                } else {
                    let mut result = vec![];

                    while k == TokenKind::Word || k == TokenKind::String {
                        let key = self.object_key()?;

                        k = self.next_token.kind;
                        if k != TokenKind::Colon && k != TokenKind::Assign {
                            return Err(RecognizerError::KeyValueSeparatorExpected(
                                token_text(k),
                                self.next_token.start,
                            ));
                        } else {
                            self.advance()?;
                            self.consume_new_lines()?;
                        }
                        result.push((key, self.expr()?));
                        k = self.next_token.kind;
                        if k == TokenKind::Newline || k == TokenKind::Comma {
                            self.advance()?;
                            k = self.consume_new_lines()?;
                        } else if k != TokenKind::RightCurly && k != TokenKind::EOF {
                            let s = format!(
                                "{} or {}",
                                token_text(TokenKind::RightCurly),
                                token_text(TokenKind::EOF)
                            );
                            return Err(RecognizerError::UnexpectedToken(
                                s,
                                token_text(self.next_token.kind),
                                self.next_token.start,
                            ));
                        }
                    }
                    Ok(ASTValue::Mapping(result))
                }
            }
        }
    }

    pub(crate) fn mapping(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.expect(TokenKind::LeftCurly) {
            Err(e) => Err(e),
            Ok(_) => match self.mapping_body() {
                Err(e) => Err(e),
                Ok(mb) => match self.expect(TokenKind::RightCurly) {
                    Err(e) => Err(e),
                    Ok(_) => Ok(mb),
                },
            },
        }
    }

    /// Parse the contents of a configuration, which should be a mapping or a list, and return
    /// the parsed value or a syntax error.
    pub fn container(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.consume_new_lines() {
            Err(e) => Err(e),
            Ok(k) => {
                if k == TokenKind::LeftCurly {
                    match self.mapping() {
                        Err(e) => Err(e),
                        Ok(mv) => match self.consume_new_lines() {
                            Err(e) => Err(e),
                            Ok(_) => Ok(mv),
                        },
                    }
                } else if k == TokenKind::LeftBracket {
                    match self.list() {
                        Err(e) => Err(e),
                        Ok(lv) => match self.consume_new_lines() {
                            Err(e) => Err(e),
                            Ok(_) => Ok(lv),
                        },
                    }
                } else if k == TokenKind::Word || k == TokenKind::String {
                    match self.mapping_body() {
                        Err(e) => Err(e),
                        Ok(lv) => match self.consume_new_lines() {
                            Err(e) => Err(e),
                            Ok(_) => Ok(lv),
                        },
                    }
                } else {
                    Err(RecognizerError::ContainerExpected(
                        token_text(k),
                        self.next_token.start,
                    ))
                }
            }
        }
    }

    pub(crate) fn power(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.primary() {
            Err(e) => Err(e),
            Ok(mut lhs) => {
                while self.next_token.kind == TokenKind::Power {
                    let spos = self.next_token.start;

                    self.advance()?;

                    let ue = self.unary_expr()?;

                    lhs = ASTValue::Binary(BinaryNode {
                        kind: TokenKind::Power,
                        left: Box::new(lhs),
                        right: Box::new(ue),
                        start: spos,
                    })
                }
                Ok(lhs)
            }
        }
    }

    pub(crate) fn unary_expr(&mut self) -> StdResult<ASTValue, RecognizerError> {
        let kind = self.next_token.kind;
        let spos = self.next_token.start;

        if kind != TokenKind::Plus
            && kind != TokenKind::Minus
            && kind != TokenKind::BitwiseComplement
            && kind != TokenKind::At
        {
            self.power()
        } else {
            match self.advance() {
                Err(e) => Err(e),
                Ok(_) => match self.not_expr() {
                    Err(e) => Err(e),
                    Ok(v) => Ok(ASTValue::Unary(UnaryNode {
                        kind,
                        operand: Box::new(v),
                        start: spos,
                    })),
                },
            }
        }
    }

    pub(crate) fn mul_expr(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.unary_expr() {
            Err(e) => Err(e),
            Ok(mut lhs) => {
                let mut kind = self.next_token.kind;

                while kind == TokenKind::Star
                    || kind == TokenKind::Slash
                    || kind == TokenKind::SlashSlash
                    || kind == TokenKind::Modulo
                {
                    let spos = self.next_token.start;

                    self.advance()?;

                    let ue = self.unary_expr()?;

                    lhs = ASTValue::Binary(BinaryNode {
                        kind,
                        left: Box::new(lhs),
                        right: Box::new(ue),
                        start: spos,
                    });
                    kind = self.next_token.kind;
                }
                Ok(lhs)
            }
        }
    }

    pub(crate) fn add_expr(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.mul_expr() {
            Err(e) => Err(e),
            Ok(mut lhs) => {
                let mut kind = self.next_token.kind;

                while kind == TokenKind::Plus || kind == TokenKind::Minus {
                    let spos = self.next_token.start;

                    self.advance()?;

                    let me = self.mul_expr()?;

                    lhs = ASTValue::Binary(BinaryNode {
                        kind,
                        left: Box::new(lhs),
                        right: Box::new(me),
                        start: spos,
                    });
                    kind = self.next_token.kind;
                }
                Ok(lhs)
            }
        }
    }

    pub(crate) fn shift_expr(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.add_expr() {
            Err(e) => Err(e),
            Ok(mut lhs) => {
                let mut kind = self.next_token.kind;

                while kind == TokenKind::LeftShift || kind == TokenKind::RightShift {
                    let spos = self.next_token.start;

                    self.advance()?;

                    let ae = self.add_expr()?;

                    lhs = ASTValue::Binary(BinaryNode {
                        kind,
                        left: Box::new(lhs),
                        right: Box::new(ae),
                        start: spos,
                    });
                    kind = self.next_token.kind;
                }
                Ok(lhs)
            }
        }
    }

    pub(crate) fn bitand_expr(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.shift_expr() {
            Err(e) => Err(e),
            Ok(mut lhs) => {
                while self.next_token.kind == TokenKind::BitwiseAnd {
                    let spos = self.next_token.start;

                    self.advance()?;

                    let se = self.shift_expr()?;

                    lhs = ASTValue::Binary(BinaryNode {
                        kind: TokenKind::BitwiseAnd,
                        left: Box::new(lhs),
                        right: Box::new(se),
                        start: spos,
                    })
                }
                Ok(lhs)
            }
        }
    }

    pub(crate) fn bitxor_expr(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.bitand_expr() {
            Err(e) => Err(e),
            Ok(mut lhs) => {
                while self.next_token.kind == TokenKind::BitwiseXor {
                    let spos = self.next_token.start;

                    self.advance()?;

                    let bae = self.bitand_expr()?;

                    lhs = ASTValue::Binary(BinaryNode {
                        kind: TokenKind::BitwiseXor,
                        left: Box::new(lhs),
                        right: Box::new(bae),
                        start: spos,
                    })
                }
                Ok(lhs)
            }
        }
    }

    pub(crate) fn bitor_expr(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.bitxor_expr() {
            Err(e) => Err(e),
            Ok(mut lhs) => {
                while self.next_token.kind == TokenKind::BitwiseOr {
                    let spos = self.next_token.start;

                    self.advance()?;

                    let bxe = self.bitxor_expr()?;

                    lhs = ASTValue::Binary(BinaryNode {
                        kind: TokenKind::BitwiseOr,
                        left: Box::new(lhs),
                        right: Box::new(bxe),
                        start: spos,
                    })
                }
                Ok(lhs)
            }
        }
    }

    pub(crate) fn comparison_operator(&mut self) -> StdResult<TokenKind, RecognizerError> {
        let mut should_advance = false;
        let mut result = self.next_token.kind;

        match self.advance() {
            Err(e) => Err(e),
            Ok(k) => {
                if result == TokenKind::Is && k == TokenKind::Not {
                    result = TokenKind::IsNot;
                    should_advance = true;
                } else if result == TokenKind::Not && k == TokenKind::In {
                    result = TokenKind::NotIn;
                    should_advance = true;
                }
                if !should_advance {
                    Ok(result)
                } else {
                    match self.advance() {
                        Err(e) => Err(e),
                        Ok(_) => Ok(result),
                    }
                }
            }
        }
    }

    pub(crate) fn comparison(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.bitor_expr() {
            Err(e) => Err(e),
            Ok(mut lhs) => {
                while COMPARISON_OPERATORS.contains(&self.next_token.kind) {
                    let spos = self.next_token.start;
                    let k = self.comparison_operator()?;
                    let boe = self.bitor_expr()?;

                    lhs = ASTValue::Binary(BinaryNode {
                        kind: k,
                        left: Box::new(lhs),
                        right: Box::new(boe),
                        start: spos,
                    })
                }
                Ok(lhs)
            }
        }
    }

    pub(crate) fn not_expr(&mut self) -> StdResult<ASTValue, RecognizerError> {
        if self.next_token.kind != TokenKind::Not {
            self.comparison()
        } else {
            let spos = self.next_token.start;

            match self.advance() {
                Err(e) => Err(e),
                Ok(_) => match self.not_expr() {
                    Err(e) => Err(e),
                    Ok(v) => Ok(ASTValue::Unary(UnaryNode {
                        kind: TokenKind::Not,
                        operand: Box::new(v),
                        start: spos,
                    })),
                },
            }
        }
    }

    pub(crate) fn and_expr(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.not_expr() {
            Err(e) => Err(e),
            Ok(mut lhs) => {
                while self.next_token.kind == TokenKind::And {
                    let spos = self.next_token.start;

                    self.advance()?;

                    let ne = self.not_expr()?;

                    lhs = ASTValue::Binary(BinaryNode {
                        kind: TokenKind::And,
                        left: Box::new(lhs),
                        right: Box::new(ne),
                        start: spos,
                    })
                }
                Ok(lhs)
            }
        }
    }

    /// Parse an expression and return an AST node representing it, or a syntax error.
    pub fn expr(&mut self) -> StdResult<ASTValue, RecognizerError> {
        match self.and_expr() {
            Err(e) => Err(e),
            Ok(mut lhs) => {
                while self.next_token.kind == TokenKind::Or {
                    let spos = self.next_token.start;

                    self.advance()?;

                    let ae = self.and_expr()?;

                    lhs = ASTValue::Binary(BinaryNode {
                        kind: TokenKind::Or,
                        left: Box::new(lhs),
                        right: Box::new(ae),
                        start: spos,
                    })
                }
                Ok(lhs)
            }
        }
    }
}

// Use a tuple struct so that we can implement PartialEq for it. This allows PartialEq to be
// derived for containing structs.

struct StringConverter(fn(&str, &Config) -> Option<Value>);

impl PartialEq for StringConverter {
    fn eq(&self, other: &Self) -> bool {
        self.0 as usize == other.0 as usize
    }
}

impl Clone for StringConverter {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl fmt::Debug for StringConverter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StringConverter({:x})", self.0 as usize)
    }
}

/// This represents a value in a configuration.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// These are the scalar values.
    Base(ScalarValue),
    /// This is a list of values.
    List(Vec<Value>),
    /// This is a mapping of strings to values.
    Mapping(HashMap<String, Value>),
    /// This is a nested (sub-) configuration.
    Config(Config),
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Value::Base(ScalarValue::Bool(value))
    }
}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        Value::Base(ScalarValue::Integer(value))
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        Value::Base(ScalarValue::Float(value))
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Value::Base(ScalarValue::String(value))
    }
}

impl From<&str> for Value {
    fn from(value: &str) -> Self {
        Value::Base(ScalarValue::String(value.to_string()))
    }
}

impl From<Complex64> for Value {
    fn from(value: Complex64) -> Self {
        Value::Base(ScalarValue::Complex(value))
    }
}

impl From<NaiveDate> for Value {
    fn from(value: NaiveDate) -> Self {
        Value::Base(ScalarValue::Date(value))
    }
}

impl From<DateTime<FixedOffset>> for Value {
    fn from(value: DateTime<FixedOffset>) -> Self {
        Value::Base(ScalarValue::DateTime(value))
    }
}

impl TryInto<i64> for Value {
    type Error = &'static str;

    fn try_into(self) -> StdResult<i64, Self::Error> {
        match self {
            Value::Base(b) => match b {
                ScalarValue::Integer(i) => Ok(i),
                _ => Err(&NOT_INTEGER),
            },
            _ => Err(&NOT_INTEGER),
        }
    }
}

impl TryInto<String> for Value {
    type Error = &'static str;

    fn try_into(self) -> StdResult<String, Self::Error> {
        match self {
            Value::Base(b) => match b {
                ScalarValue::String(s) => Ok(s),
                _ => Err(&NOT_STRING),
            },
            _ => Err(&NOT_STRING),
        }
    }
}

impl TryInto<f64> for Value {
    type Error = &'static str;

    fn try_into(self) -> StdResult<f64, Self::Error> {
        match self {
            Value::Base(b) => match b {
                ScalarValue::Float(f) => Ok(f),
                _ => Err(&NOT_FLOAT),
            },
            _ => Err(&NOT_FLOAT),
        }
    }
}

impl TryInto<Complex64> for Value {
    type Error = &'static str;

    fn try_into(self) -> StdResult<Complex64, Self::Error> {
        match self {
            Value::Base(b) => match b {
                ScalarValue::Complex(c) => Ok(c),
                _ => Err(&NOT_COMPLEX),
            },
            _ => Err(&NOT_COMPLEX),
        }
    }
}

impl TryInto<NaiveDate> for Value {
    type Error = &'static str;

    fn try_into(self) -> StdResult<NaiveDate, Self::Error> {
        match self {
            Value::Base(b) => match b {
                ScalarValue::Date(nd) => Ok(nd),
                _ => Err(&NOT_DATE),
            },
            _ => Err(&NOT_DATE),
        }
    }
}

impl TryInto<DateTime<FixedOffset>> for Value {
    type Error = &'static str;

    fn try_into(self) -> StdResult<DateTime<FixedOffset>, Self::Error> {
        match self {
            Value::Base(b) => match b {
                ScalarValue::DateTime(dt) => Ok(dt),
                _ => Err(&NOT_DATETIME),
            },
            _ => Err(&NOT_DATETIME),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Base(b) => write!(f, "{}", b),
            Value::List(lv) => {
                let mut parts = vec![];

                for item in lv {
                    parts.push(format!("{}", item));
                }
                let s = parts.join(", ");
                write!(f, "[{}]", s)
            }
            Value::Mapping(mv) => {
                let mut parts = vec![];

                for (k, v) in mv.iter() {
                    parts.push(format!("{}: {}", k, v));
                }
                let s = parts.join(", ");
                write!(f, "{{{}}}", s)
            }
            Value::Config(cv) => write!(f, "{}", cv),
        }
    }
}

impl Value {
    /*
     * The following are useful if you just want to panic on something unexpected, e.g. in tests
     */
    /// Expect a value to be a string and return it. Panic if it's not the expected type.
    pub fn as_string(&self) -> String {
        let mut result: Option<String> = None;

        if let Value::Base(sv) = self {
            if let ScalarValue::String(s) = sv {
                result = Some(s.clone());
            }
        }
        match result {
            None => panic!("expected string value but got {:?}", self),
            Some(v) => v,
        }
    }

    /// Expect a value to be an integer and return it. Panic if it's not the expected type.
    pub fn as_i64(&self) -> i64 {
        let mut result: Option<i64> = None;

        if let Value::Base(sv) = self {
            if let ScalarValue::Integer(i) = sv {
                result = Some(*i);
            }
        }
        match result {
            None => panic!("expected integer value but got {:?}", self),
            Some(v) => v,
        }
    }

    /// Expect a value to be a floating-point value and return it. Panic if it's not the expected type.
    pub fn as_f64(&self) -> f64 {
        let mut result: Option<f64> = None;

        if let Value::Base(sv) = self {
            if let ScalarValue::Float(f) = sv {
                result = Some(*f);
            }
        }
        match result {
            None => panic!("expected floating-point value but got {:?}", self),
            Some(v) => v,
        }
    }

    /// Expect a value to be a complex number and return it. Panic if it's not the expected type.
    pub fn as_c64(&self) -> Complex64 {
        let mut result: Option<Complex64> = None;

        if let Value::Base(sv) = self {
            if let ScalarValue::Complex(c) = sv {
                result = Some(*c);
            }
        }
        match result {
            None => panic!("expected complex value but got {:?}", self),
            Some(v) => v,
        }
    }

    /// Expect a value to be a Boolean and return it. Panic if it's not the expected type.
    pub fn as_bool(&self) -> bool {
        let mut result: Option<bool> = None;

        if let Value::Base(sv) = self {
            if let ScalarValue::Bool(b) = sv {
                result = Some(*b);
            }
        }
        match result {
            None => panic!("expected boolean value but got {:?}", self),
            Some(v) => v,
        }
    }

    /// Expect a value to be a date and return it. Panic if it's not the expected type.
    pub fn as_date(&self) -> NaiveDate {
        let mut result: Option<NaiveDate> = None;

        if let Value::Base(sv) = self {
            if let ScalarValue::Date(nd) = sv {
                result = Some(*nd);
            }
        }
        match result {
            None => panic!("expected date value but got {:?}", self),
            Some(v) => v,
        }
    }

    /// Expect a value to be a date/time and return it. Panic if it's not the expected type.
    pub fn as_datetime(&self) -> DateTime<FixedOffset> {
        let mut result: Option<DateTime<FixedOffset>> = None;

        if let Value::Base(sv) = self {
            if let ScalarValue::DateTime(dt) = sv {
                result = Some(*dt);
            }
        }
        match result {
            None => panic!("expected date/time value but got {:?}", self),
            Some(v) => v,
        }
    }

    /// Expect a value to be a list and return it. Panic if it's not the expected type.
    pub fn as_list(&self) -> Vec<Value> {
        let mut result: Option<Vec<Value>> = None;

        if let Value::List(lv) = self {
            result = Some(lv.clone());
        }
        match result {
            None => panic!("expected list value but got {:?}", self),
            Some(v) => v,
        }
    }

    /// Expect a value to be a mapping and return it. Panic if it's not the expected type.
    pub fn as_mapping(&self) -> HashMap<String, Value> {
        let mut result: Option<HashMap<String, Value>> = None;

        if let Value::Mapping(mv) = self {
            result = Some(mv.clone());
        }
        match result {
            None => panic!("expected mapping value but got {:?}", self),
            Some(v) => v,
        }
    }

    /// Expect a value to be a sub-configuration and return it. Panic if it's not the expected type.
    pub fn as_config(&self) -> Config {
        let mut result: Option<Config> = None;

        if let Value::Config(c) = self {
            result = Some(c.clone());
        }
        match result {
            None => panic!("expected config value but got {:?}", self),
            Some(v) => v,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum InternalValue {
    Base(Value), // has been evaluated
    List(Vec<Rc<RefCell<InternalValue>>>),
    Mapping(HashMap<String, Rc<RefCell<InternalValue>>>),
    AST(ASTValue),
}

impl InternalValue {
    /*
        fn is_float(&self) -> bool {
            match self {
                InternalValue::Base(cv) => match cv {
                    ConfigValue::Base(b) => match b {
                        ScalarValue::Float(_) => true,
                        _ => false,
                    },
                    _ => false,
                },
                _ => false,
            }
        }

        fn is_complex(&self) -> bool {
            match self {
                InternalConfigValue::Base(cv) => match cv {
                    ConfigValue::Base(b) => match b {
                        ScalarValue::Complex(_) => true,
                        _ => false,
                    },
                    _ => false,
                },
                _ => false,
            }
        }

        fn is_integer(&self) -> bool {
            match self {
                InternalConfigValue::Base(cv) => match cv {
                    ConfigValue::Base(b) => match b {
                        ScalarValue::Integer(_) => true,
                        _ => false,
                    },
                    _ => false,
                },
                _ => false,
            }
        }

        fn is_bool(&self) -> bool {
            match self {
                InternalConfigValue::Base(cv) => match cv {
                    ConfigValue::Base(b) => match b {
                        ScalarValue::Bool(_) => true,
                        _ => false,
                    },
                    _ => false,
                },
                _ => false,
            }
        }

        fn is_sequence(&self) -> bool {
            match self {
                InternalConfigValue::List(_) => true,
                InternalConfigValue::Base(cv) => match cv {
                    ConfigValue::List(_) => true,
                    _ => false,
                },
                _ => false,
            }
        }

        fn is_mapping(&self) -> bool {
            match self {
                InternalConfigValue::Mapping(_) => true,
                InternalConfigValue::Base(cv) => match cv {
                    ConfigValue::Mapping(_) => true,
                    _ => false,
                },
                _ => false,
            }
        }
    */

    fn make_int(i: i64) -> Self {
        InternalValue::Base(Value::Base(ScalarValue::Integer(i)))
    }

    fn make_float(f: f64) -> Self {
        InternalValue::Base(Value::Base(ScalarValue::Float(f)))
    }

    fn make_complex(c: Complex64) -> Self {
        InternalValue::Base(Value::Base(ScalarValue::Complex(c)))
    }

    fn make_string(s: String) -> Self {
        InternalValue::Base(Value::Base(ScalarValue::String(s)))
    }
}

/// This is the type of error returned from the high-level API for CFG configurations.
#[derive(Debug, PartialEq)]
pub enum ConfigError {
    /// This error is returned if the configuration text couldn't be parsed as
    /// valid CFG source. The underlying parser error is returned, which should
    /// contain location information.
    SyntaxError(RecognizerError),
    /// This error is returned if an attempt is made to query a configuration
    /// into which nothing has been loaded.
    NotLoaded,
    /// This error is returned if a file loaded as a top-level configuration is
    /// not a mapping or mapping body.
    MappingExpected,
    /// This error is returned if a string was expected, but not found. The
    /// location where it was expected is returned. This might be the location
    /// of an @ operator, whose operand must be a string be cause it represents
    /// the path to a file to be included as a sub-configuration.
    StringExpected(Location),
    /// This error is returned if a duplicate key is found when parsing a
    /// configuration. The key, the duplicate location and the original location
    /// are returned.
    DuplicateKey(String, Location, Location),
    /// This error is returned if a specified path is invalid (e.g. couldn't be
    /// canonocalized). The offending path is provided.
    BadFilePath(String),
    /// This error is returned if a file couldn't be found. The path that
    /// couldn't be found is provided.
    FileNotFound(String),
    /// This error is returned if a file couldn't be opened for reading. The
    /// path that couldn't be read is provided.
    FileReadFailed(String),
    /// This error is returned if an identifier is seen, but no lookup context
    /// has been provided.
    NoContext,
    /// This error is returned if an identifier is not a key in a specified
    /// lookup context.
    UnknownVariable(String, Location),
    /// This error is returned if a key is not present in a configuration or
    /// path therein. If the absence is in a path, the location within that
    /// path is returned, along with the missing key.
    NotPresent(String, Option<Location>),
    /// This error is returned if a string couldn't be parsed as a valid path.
    /// The underlying parser error is returned, which will include location
    /// information.
    InvalidPath(RecognizerError),
    /// This error is returned if a path operand isn't valid for the current
    /// container (e.g. string index for a list, or numeric index for a mapping).
    /// The source location where the error occurred are returned.
    InvalidPathOperand(Location),
    /// This error is returned if an index value is out of range. The bad index
    /// value and the source location where it was found are returned.
    IndexOutOfRange(i64, Location),
    /// This error is returned if an evaluation failed. A source location near
    /// to where the failure occurred is returned.
    EvaluationFailed(Location),
    /// This error is returned if a special string (back-tick string) couldn't
    /// be converted. The special string which couldn't be handled is returned.
    ConversionError(String),
    /// This error is returned if a reference cycle is detected. A list of the
    /// reference paths in the cycle, together with their locations, is returned.
    CircularReferenceError(Vec<(String, Location)>),
}

#[derive(Debug, PartialEq)]
pub(crate) enum PathElement<'a> {
    Attribute(&'a Token),
    IndexedAccess(&'a ASTValue),
    SliceAccess(&'a ASTValue),
}

/// Represents a CFG configuration.
///
#[derive(Debug, Clone, PartialEq)]
pub struct Config {
    /// If `true`, loaded configurations aren't allowed to have duplicate keys.
    /// If `false`, duplicate keys are allowed, and values encountered later
    /// overwrite values encountered earlier for the same key.
    pub no_duplicates: bool,
    //    pub strict_conversions: bool,
    root_dir: String,
    path: String,
    include_path: Vec<String>,
    string_converter: StringConverter,
    context: Option<HashMap<String, Value>>,
    data: Rc<RefCell<InternalValue>>,
    refs_seen: RefCell<HashSet<(String, Location)>>,
}

impl fmt::Display for Config {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let fname = Path::new(&self.path)
            .file_name()
            .expect("couldn't get file name")
            .to_str()
            .expect("couldn't convert file name to Unicode");
        let num_items = match &*self.data.borrow() {
            InternalValue::Mapping(hm) => hm.len(),
            _ => panic!("Unexpected type for data"),
        };
        write!(f, "Config(").unwrap();
        write!(f, "{}, {} items", fname, num_items).unwrap();
        write!(f, ")")
    }
}

fn make_node(v: InternalValue) -> Rc<RefCell<InternalValue>> {
    Rc::new(RefCell::new(v))
}

fn default_string_converter(s: &str, cfg: &Config) -> Option<Value> {
    let mut result = None;

    fn get_i32(caps: &Captures, i: usize) -> i32 {
        caps.get(i).unwrap().as_str().parse::<i32>().unwrap()
    }

    fn get_u32(caps: &Captures, i: usize) -> u32 {
        caps.get(i).unwrap().as_str().parse::<u32>().unwrap()
    }

    /*
        fn get_str<'a>(caps: &'a Captures, i: usize) -> &'a str {
            caps.get(i).unwrap().as_str()
        }
    */

    match ISO_DATETIME_PATTERN.captures(s) {
        Some(groups) => {
            let y = get_i32(&groups, 1);
            let m = get_u32(&groups, 2);
            let d = get_u32(&groups, 3);
            let has_time = groups.get(5).is_some();
            let nd = NaiveDate::from_ymd(y, m, d);

            if !has_time {
                result = Some(Value::from(nd));
            } else {
                let h = get_u32(&groups, 8);
                let m = get_u32(&groups, 9);
                let s = get_u32(&groups, 10);
                let has_offset = groups.get(13).is_some();
                let nanos = match groups.get(11) {
                    None => 0,
                    Some(v) => (v.as_str().parse::<f64>().unwrap() * 1.0e9) as u32,
                };
                let time = NaiveTime::from_hms_nano(h, m, s, nanos);
                let datetime = NaiveDateTime::new(nd, time);

                let offsecs = if !has_offset {
                    0
                } else {
                    let sign = if groups.get(13).unwrap().as_str() == "-" {
                        -1
                    } else {
                        1
                    };
                    let oh = get_i32(&groups, 14);
                    let om = get_i32(&groups, 15);
                    let os = match groups.get(17) {
                        None => 0,
                        Some(v) => v.as_str().parse::<i32>().unwrap(),
                    };
                    sign * (os + om * 60 + oh * 3600)
                };
                let offset = FixedOffset::east(offsecs);
                let dt = DateTime::<FixedOffset>::from_utc(datetime, offset);
                result = Some(Value::from(dt));
            }
        }
        None => match ENV_VALUE_PATTERN.captures(s) {
            Some(groups) => {
                let name = groups.get(1).unwrap().as_str();

                match env::var(name) {
                    Err(_) => {
                        let has_pipe = groups.get(2).is_some();

                        if !has_pipe {
                            result = Some(Value::Base(ScalarValue::None));
                        } else {
                            let s = groups.get(3).unwrap().as_str();

                            result = Some(Value::from(s))
                        }
                    }
                    Ok(v) => result = Some(Value::from(v)),
                }
            }
            None => match INTERPOLATION_PATTERN.captures(s) {
                None => {}
                Some(_) => {
                    let mut failed = false;
                    let mut cp = 0;
                    let mut parts = vec![];

                    for m in INTERPOLATION_PATTERN.find_iter(s) {
                        let sp = m.start();
                        let ep = m.end();
                        let path = &s[sp + 2..ep - 1];

                        if cp < sp {
                            parts.push(s[cp..sp].to_string());
                        }
                        match cfg.get(path) {
                            Err(_) => {
                                failed = true;
                                break;
                            }
                            Ok(v) => {
                                parts.push(format!("{}", v));
                            }
                        }
                        cp = ep;
                    }
                    if !failed {
                        if cp < s.len() {
                            parts.push(s[cp..s.len()].to_string());
                        }
                        let rv = parts.join("");
                        result = Some(Value::from(rv.as_str()));
                    }
                }
            },
        },
    }
    result
}

fn find_in_path(fname: &str, path: &[String]) -> Option<String> {
    for entry in path {
        let mut p = PathBuf::new();

        p.push(entry);
        p.push(fname);

        let path = p.as_path();
        if path.exists() {
            match path.to_str() {
                None => return None,
                Some(s) => return Some(s.to_string()),
            }
        }
    }
    None
}

pub(crate) fn parse_path(s: &str) -> StdResult<ASTValue, RecognizerError> {
    let c = Cursor::new(s);

    match Parser::new(Box::new(c)) {
        Err(e) => Err(e),
        Ok(mut parser) => {
            if parser.next_token.kind != TokenKind::Word {
                return Err(RecognizerError::UnexpectedToken(
                    token_text(TokenKind::Word),
                    token_text(parser.next_token.kind),
                    parser.next_token.start,
                ));
            }
            match parser.primary() {
                Ok(av) => {
                    if !parser.at_end() {
                        Err(RecognizerError::TrailingText(parser.next_token.start))
                    } else {
                        Ok(av)
                    }
                }
                Err(e) => Err(e),
            }
        }
    }
}

// since Rust doesn't implement generator functions, we just unpack a path into a sequence
// using this function.
pub(crate) fn unpack_path<'a>(node: &'a ASTValue) -> Vec<PathElement<'a>> {
    let mut path = vec![];

    fn visit<'a>(path: &mut Vec<PathElement<'a>>, node: &'a ASTValue) {
        match node {
            ASTValue::TokenValue(t) => path.push(PathElement::Attribute(&t)),
            ASTValue::Unary(un) => visit(path, &un.operand),
            ASTValue::Binary(bn) => {
                visit(path, &bn.left);
                match bn.kind {
                    TokenKind::Dot => match &*bn.right {
                        ASTValue::TokenValue(t) => path.push(PathElement::Attribute(&t)),
                        _ => panic!("unexpected node with attribute access: {:?}", bn.right),
                    },
                    TokenKind::LeftBracket => path.push(PathElement::IndexedAccess(&bn.right)),
                    TokenKind::Colon => path.push(PathElement::SliceAccess(&bn.right)),
                    _ => panic!("unpack_path not implemented for {:?}", bn),
                }
            }
            _ => panic!("unpack_path not implemented for {:?}", node),
        }
    }

    visit(&mut path, node);
    path
}

pub(crate) fn to_source(node: &ASTValue) -> String {
    let path = unpack_path(node);
    let mut parts = vec![];

    for (i, element) in path.iter().enumerate() {
        match element {
            PathElement::Attribute(t) => {
                if i > 0 {
                    parts.push(".".to_string());
                }
                parts.push(t.text.clone());
            }
            PathElement::IndexedAccess(index) => {
                parts.push("[".to_string());
                parts.push(to_source(index));
                parts.push("]".to_string());
            }
            PathElement::SliceAccess(slice) => {
                parts.push("[".to_string());
                match slice {
                    ASTValue::Slice(_, start, stop, step) => {
                        if let Some(v) = &**start {
                            parts.push(to_source(v));
                        }
                        parts.push(":".to_string());
                        if let Some(v) = &**stop {
                            parts.push(to_source(v));
                        }
                        if let Some(v) = &**step {
                            parts.push(":".to_string());
                            parts.push(to_source(v));
                        }
                    }
                    _ => panic!("unexpected in slice element: {:?}", slice),
                }
                parts.push("]".to_string());
            }
        }
    }
    parts.join("")
}

impl Default for Config {
    fn default() -> Self {
        Self::new()
    }
}

impl Config {
    /// Return an empty configuration with default settings.
    pub fn new() -> Self {
        Self {
            no_duplicates: true,
            //            strict_conversions: true,
            root_dir: "".to_string(),
            path: "".to_string(),
            include_path: vec![],
            string_converter: StringConverter(default_string_converter),
            context: None,
            data: make_node(InternalValue::Mapping(HashMap::new())),
            refs_seen: RefCell::new(HashSet::new()),
        }
    }

    /// Return a new configuration loaded from the file named by `file_path`.
    pub fn from_file(file_path: &str) -> StdResult<Self, ConfigError> {
        let mut result = Config::new();

        match result.load_from_file(file_path) {
            Ok(()) => Ok(result),
            Err(e) => Err(e),
        }
    }

    /// Add the directory `dir` to the end of the include path.
    pub fn add_include(&mut self, dir: &str) {
        self.include_path.push(dir.to_string());
    }

    fn try_open_file(&self, path: &str) -> StdResult<File, ConfigError> {
        match File::open(path) {
            Err(e) => {
                warn!("File read failed for {}: {:?}", path, e);
                Err(ConfigError::FileReadFailed(path.to_string()))
            }
            Ok(f) => Ok(f),
        }
    }

    fn set_path(&mut self, file_path: &str) -> bool {
        let p = PathBuf::from(file_path);
        let mut failed = false;

        match canonicalize(&p) {
            Ok(cp) => match cp.to_str() {
                Some(s) => {
                    self.path = s.to_string();
                    match cp.parent() {
                        Some(pp) => match pp.to_str() {
                            None => failed = true,
                            Some(s) => self.root_dir = s.to_string(),
                        },
                        None => failed = true,
                    }
                }
                None => {
                    warn!("failed to convert {:?} to str", cp);
                    failed = true
                }
            },
            Err(_) => {
                warn!("failed to canonicalize {:?}", p);
                failed = true
            }
        };
        failed
    }

    /// Load the configuration from the file named by `file_path`.
    pub fn load_from_file(&mut self, file_path: &str) -> StdResult<(), ConfigError> {
        match self.try_open_file(file_path) {
            Err(e) => Err(e),
            Ok(f) => match self.load(Box::new(f)) {
                Err(e) => Err(e),
                Ok(()) => {
                    if self.set_path(file_path) {
                        Err(ConfigError::BadFilePath(file_path.to_string()))
                    } else {
                        Ok(())
                    }
                }
            },
        }
    }

    fn wrap_mapping(
        &self,
        items: &[(Token, ASTValue)],
    ) -> StdResult<HashMap<String, Rc<RefCell<InternalValue>>>, ConfigError> {
        // only allocate map when needed
        let mut maybe_seen: Option<HashMap<String, Location>> = if self.no_duplicates {
            Some(HashMap::new())
        } else {
            None
        };
        let mut result: HashMap<String, Rc<RefCell<InternalValue>>> = HashMap::new();

        for (t, v) in items.iter() {
            let key: &str;

            match &t.value {
                ScalarValue::Identifier(iv) => {
                    key = &iv;
                }
                ScalarValue::String(sv) => {
                    key = &sv;
                }
                _ => panic!("non-string key encountered"),
            }
            match maybe_seen {
                None => {
                    result.insert(key.to_string(), make_node(InternalValue::AST(v.clone())));
                }
                Some(ref mut seen) => match seen.get(key) {
                    Some(orig_loc) => {
                        return Err(ConfigError::DuplicateKey(
                            key.to_string(),
                            t.start,
                            *orig_loc,
                        ));
                    }
                    None => {
                        seen.insert(key.to_string(), t.start.clone());
                        result.insert(key.to_string(), make_node(InternalValue::AST(v.clone())));
                    }
                },
            }
        }
        Ok(result)
    }

    fn wrap_sequence(&self, items: &[ASTValue]) -> Vec<Rc<RefCell<InternalValue>>> {
        let mut result = vec![];

        for item in items.iter() {
            result.push(make_node(InternalValue::AST(item.clone())));
        }
        result
    }

    /// Load the configuration from the reader `r`.
    pub fn load(&mut self, r: Box<dyn Read>) -> StdResult<(), ConfigError> {
        let mut parser = Parser::new(r).expect("unable to create parser");

        match parser.container() {
            Err(e) => Err(ConfigError::SyntaxError(e)),
            Ok(node) => {
                // It must be a mapping, as we're at the root level
                match node {
                    ASTValue::Mapping(items) => match self.wrap_mapping(&items) {
                        Err(e) => Err(e),
                        Ok(data) => {
                            self.data = make_node(InternalValue::Mapping(data));
                            Ok(())
                        }
                    },
                    _ => Err(ConfigError::MappingExpected),
                }
            }
        }
    }

    /// Set the given hashmap `context` as the place to look up identifiers
    /// encountered in the configuration.
    pub fn set_context(&mut self, context: HashMap<String, Value>) {
        self.context = Some(context)
    }

    fn eval_at(&self, node: &ASTValue, loc: Location) -> StdResult<InternalValue, ConfigError> {
        match self.evaluate(node) {
            Err(e) => Err(e),
            Ok(v) => match v {
                InternalValue::Base(cv) => match cv {
                    Value::Base(tv) => match tv {
                        ScalarValue::String(mut fname) => {
                            let mut dirs = vec![];
                            let p = Path::new(&fname);

                            if p.is_absolute() {
                                dirs.push(p.parent().unwrap().to_str().unwrap().to_string());
                                fname = p.file_name().unwrap().to_str().unwrap().to_string();
                            } else {
                                dirs.push(self.root_dir.clone());
                                dirs.extend_from_slice(&self.include_path);
                            }

                            match find_in_path(&fname, &dirs) {
                                None => Err(ConfigError::FileNotFound(fname.to_string())),
                                Some(p) => {
                                    match self.try_open_file(&p) {
                                        Err(e) => Err(e),
                                        Ok(f) => {
                                            let mut parser = Parser::new(Box::new(f))
                                                .expect("unable to create parser");

                                            match parser.container() {
                                                Err(e) => Err(ConfigError::SyntaxError(e)),
                                                Ok(node) => match node {
                                                    ASTValue::Mapping(items) => match self
                                                        .wrap_mapping(&items)
                                                    {
                                                        Err(e) => Err(e),
                                                        Ok(data) => {
                                                            // make a new config with the appropriate data
                                                            let data = make_node(
                                                                InternalValue::Mapping(data),
                                                            );
                                                            let mut cfg = Config::new();

                                                            cfg.no_duplicates = self.no_duplicates;
                                                            cfg.context = self.context.clone();
                                                            cfg.include_path =
                                                                self.include_path.clone();
                                                            cfg.set_path(&p);
                                                            cfg.data = data;
                                                            Ok(InternalValue::Base(Value::Config(
                                                                cfg,
                                                            )))
                                                        }
                                                    },
                                                    ASTValue::List(items) => {
                                                        let mut result = vec![];

                                                        for item in items {
                                                            result.push(make_node(
                                                                InternalValue::AST(item.clone()),
                                                            ));
                                                        }
                                                        Ok(InternalValue::List(result))
                                                    }
                                                    _ => {
                                                        todo!("included data is neither mapping nor list");
                                                    }
                                                },
                                            }
                                        }
                                    }
                                    //                                    match Config::from_file(&p) {
                                    //                                        Err(e) => Err(e),
                                    //                                        Ok(cfg) => {
                                    //                                            Ok(InternalConfigValue::Base(ConfigValue::Config(cfg)))
                                    //                                        }
                                    //                                    }
                                }
                            }
                        }
                        _ => Err(ConfigError::StringExpected(loc)),
                    },
                    _ => Err(ConfigError::StringExpected(loc)),
                },
                _ => todo!("unhandled internal config value"),
            },
        }
    }

    fn eval_reference(&self, node: &ASTValue) -> StdResult<InternalValue, ConfigError> {
        self.get_from_path(node)
    }

    fn eval_negation(
        &self,
        node: &ASTValue,
        loc: Location,
    ) -> StdResult<InternalValue, ConfigError> {
        match self.evaluate(node) {
            Err(e) => Err(e),
            Ok(v) => match &v {
                InternalValue::Base(cv) => match cv {
                    Value::Base(tv) => match tv {
                        ScalarValue::Integer(i) => Ok(InternalValue::make_int(-i)),
                        ScalarValue::Float(f) => Ok(InternalValue::make_float(-f)),
                        ScalarValue::Complex(c) => Ok(InternalValue::make_complex(-c)),
                        _ => {
                            warn!("cannot negate {:?}", v);
                            Err(ConfigError::EvaluationFailed(loc))
                        }
                    },
                    _ => {
                        warn!("cannot negate {:?}", v);
                        Err(ConfigError::EvaluationFailed(loc))
                    }
                },
                _ => {
                    warn!("cannot negate {:?}", v);
                    Err(ConfigError::EvaluationFailed(loc))
                }
            },
        }
    }

    fn eval_unary(&self, node: &UnaryNode) -> StdResult<InternalValue, ConfigError> {
        match node.kind {
            TokenKind::At => self.eval_at(&node.operand, node.start),
            TokenKind::Dollar => self.eval_reference(&node.operand),
            TokenKind::Minus => self.eval_negation(&node.operand, node.start),
            _ => todo!("unhandled unary kind: {:?}", node.kind),
        }
    }

    fn get_operands(
        &self,
        node: &BinaryNode,
    ) -> StdResult<(InternalValue, InternalValue), ConfigError> {
        let lhs = self.evaluate(&node.left)?;
        let rhs = self.evaluate(&node.right)?;
        Ok((lhs, rhs))
    }

    fn merge_dicts(
        &self,
        left: &HashMap<String, Rc<RefCell<InternalValue>>>,
        right: &HashMap<String, Rc<RefCell<InternalValue>>>,
    ) -> StdResult<HashMap<String, Rc<RefCell<InternalValue>>>, ConfigError> {
        let mut result = left.clone();

        for (k, v) in right.iter() {
            let key = k.clone();

            match result.get(k) {
                None => {
                    // it's not in the target, so copy it over
                    result.insert(key, v.clone());
                }
                Some(ov) => {
                    // it's in the target with value ov. If ov and v are both mappings, merge them
                    // else overwrite target (left) with source (right). Either might be ASTs, and
                    // if so they need evaluating
                    let target: InternalValue;

                    if let InternalValue::AST(node) = &*ov.borrow() {
                        target = self.evaluate(&node)?;
                    } else {
                        target = ov.borrow().clone();
                    }
                    if let InternalValue::Mapping(ref tm) = target {
                        let source: InternalValue;

                        if let InternalValue::AST(node) = &*v.borrow() {
                            source = self.evaluate(&node)?;
                        } else {
                            source = ov.borrow().clone();
                        }
                        if let InternalValue::Mapping(ref sm) = source {
                            let merged = self.merge_dicts(tm, sm)?;

                            result.insert(key, make_node(InternalValue::Mapping(merged)));
                        } else {
                            result.insert(key, v.clone());
                        }
                    } else {
                        result.insert(key, v.clone());
                    }
                }
            }
        }
        Ok(result)
    }

    fn eval_add(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_int(ilhs + irhs))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        Ok(InternalValue::make_float(*ilhs as f64 + frhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        let clhs = Complex64::new(*ilhs as f64, 0.0);

                                        Ok(InternalValue::make_complex(clhs + crhs))
                                    }
                                    _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                                },
                                ScalarValue::Float(flhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_float(flhs + *irhs as f64))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        Ok(InternalValue::make_float(flhs + frhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        let clhs = Complex64::new(*flhs, 0.0);

                                        Ok(InternalValue::make_complex(clhs + crhs))
                                    }
                                    _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                                },
                                ScalarValue::Complex(clhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        let crhs = Complex64::new(*irhs as f64, 0.0);

                                        Ok(InternalValue::make_complex(clhs + crhs))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        let crhs = Complex64::new(*frhs, 0.0);

                                        Ok(InternalValue::make_complex(clhs + crhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        Ok(InternalValue::make_complex(clhs + crhs))
                                    }
                                    _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                                },
                                ScalarValue::String(slhs) => match &svrhs {
                                    ScalarValue::String(srhs) => {
                                        let mut r = String::new();

                                        r.push_str(slhs);
                                        r.push_str(srhs);
                                        Ok(InternalValue::make_string(r))
                                    }
                                    _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                                },
                                _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                            },
                            _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                        },
                        Value::List(seqlhs) => match &cvrhs {
                            Value::List(seqrhs) => {
                                let mut result = seqlhs.clone();

                                result.extend(seqrhs.iter().cloned());
                                Ok(InternalValue::Base(Value::List(result)))
                            }
                            _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                        },
                        _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                },
                InternalValue::List(llhs) => match &rhs {
                    InternalValue::List(lrhs) => {
                        let mut result = llhs.clone();

                        result.extend(lrhs.iter().cloned());
                        Ok(InternalValue::List(result))
                    }
                    InternalValue::Base(b) => match b {
                        Value::List(seq) => match self.base_unwrap_list(llhs, false) {
                            Err(e) => Err(e),
                            Ok(mut result) => {
                                result.extend(seq.iter().cloned());
                                Ok(InternalValue::Base(Value::List(result)))
                            }
                        },
                        _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                },
                InternalValue::Mapping(mlhs) => match &rhs {
                    InternalValue::Mapping(mrhs) => match self.merge_dicts(mlhs, mrhs) {
                        Err(e) => Err(e),
                        Ok(v) => Ok(InternalValue::Mapping(v)),
                    },
                    _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                },
                _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
            },
        }
    }

    fn eval_subtract(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_int(ilhs - irhs))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        Ok(InternalValue::make_float(*ilhs as f64 - frhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        let clhs = Complex64::new(*ilhs as f64, 0.0);

                                        Ok(InternalValue::make_complex(clhs - crhs))
                                    }
                                    _ => todo!("cannot subtract {:?} from {:?}", rhs, lhs),
                                },
                                ScalarValue::Float(flhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_float(flhs - *irhs as f64))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        Ok(InternalValue::make_float(flhs - frhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        let clhs = Complex64::new(*flhs, 0.0);

                                        Ok(InternalValue::make_complex(clhs - crhs))
                                    }
                                    _ => todo!("cannot subtract {:?} from {:?}", rhs, lhs),
                                },
                                ScalarValue::Complex(clhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        let crhs = Complex64::new(*irhs as f64, 0.0);

                                        Ok(InternalValue::make_complex(clhs - crhs))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        let crhs = Complex64::new(*frhs, 0.0);

                                        Ok(InternalValue::make_complex(clhs - crhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        Ok(InternalValue::make_complex(clhs - crhs))
                                    }
                                    _ => todo!("cannot subtract {:?} from {:?}", rhs, lhs),
                                },
                                _ => todo!("cannot subtract {:?} from {:?}", rhs, lhs),
                            },
                            _ => todo!("cannot subtract {:?} from {:?}", rhs, lhs),
                        },
                        _ => todo!("cannot subtract {:?} from {:?}", rhs, lhs),
                    },
                    _ => todo!("cannot subtract {:?} from {:?}", rhs, lhs),
                },
                InternalValue::Mapping(mlhs) => match &rhs {
                    InternalValue::Mapping(mrhs) => {
                        let mut result = mlhs.clone();

                        for (k, _) in mrhs.iter() {
                            match result.get(k) {
                                None => {}
                                Some(_) => {
                                    result.remove(k);
                                }
                            }
                        }

                        Ok(InternalValue::Mapping(result))
                    }
                    _ => todo!("cannot subtract {:?} from {:?}", rhs, lhs),
                },
                _ => todo!("cannot subtract {:?} from {:?}", rhs, lhs),
            },
        }
    }

    fn eval_multiply(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_int(ilhs * irhs))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        Ok(InternalValue::make_float(*ilhs as f64 * frhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        let clhs = Complex64::new(*ilhs as f64, 0.0);

                                        Ok(InternalValue::make_complex(clhs * crhs))
                                    }
                                    _ => todo!("cannot multiply {:?} by {:?}", lhs, rhs),
                                },
                                ScalarValue::Float(flhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_float(flhs * *irhs as f64))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        Ok(InternalValue::make_float(flhs * frhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        let clhs = Complex64::new(*flhs, 0.0);

                                        Ok(InternalValue::make_complex(clhs * crhs))
                                    }
                                    _ => todo!("cannot multiply {:?} by {:?}", lhs, rhs),
                                },
                                ScalarValue::Complex(clhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        let crhs = Complex64::new(*irhs as f64, 0.0);

                                        Ok(InternalValue::make_complex(clhs * crhs))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        let crhs = Complex64::new(*frhs, 0.0);

                                        Ok(InternalValue::make_complex(clhs * crhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        Ok(InternalValue::make_complex(clhs * crhs))
                                    }
                                    _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                                },
                                _ => todo!("cannot multiply {:?} by {:?}", lhs, rhs),
                            },
                            _ => todo!("cannot multiply {:?} by {:?}", lhs, rhs),
                        },
                        _ => todo!("cannot multiply {:?} by {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot multiply {:?} by {:?}", lhs, rhs),
                },
                _ => todo!("cannot multiply {:?} by {:?}", lhs, rhs),
            },
        }
    }

    fn eval_divide(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => Ok(InternalValue::make_float(
                                        (*ilhs as f64) / (*irhs as f64),
                                    )),
                                    ScalarValue::Float(frhs) => {
                                        Ok(InternalValue::make_float(*ilhs as f64 * frhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        let clhs = Complex64::new(*ilhs as f64, 0.0);

                                        Ok(InternalValue::make_complex(clhs / crhs))
                                    }
                                    _ => todo!("cannot divide {:?} by {:?}", lhs, rhs),
                                },
                                ScalarValue::Float(flhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_float(flhs - *irhs as f64))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        Ok(InternalValue::make_float(flhs / frhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        let clhs = Complex64::new(*flhs, 0.0);

                                        Ok(InternalValue::make_complex(clhs / crhs))
                                    }
                                    _ => todo!("cannot divide {:?} by {:?}", lhs, rhs),
                                },
                                ScalarValue::Complex(clhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        let crhs = Complex64::new(*irhs as f64, 0.0);

                                        Ok(InternalValue::make_complex(clhs / crhs))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        let crhs = Complex64::new(*frhs, 0.0);

                                        Ok(InternalValue::make_complex(clhs / crhs))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        Ok(InternalValue::make_complex(clhs / crhs))
                                    }
                                    _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                                },
                                _ => todo!("cannot divide {:?} by {:?}", lhs, rhs),
                            },
                            _ => todo!("cannot divide {:?} by {:?}", lhs, rhs),
                        },
                        _ => todo!("cannot divide {:?} by {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot divide {:?} by {:?}", lhs, rhs),
                },
                _ => todo!("cannot divide {:?} by {:?}", lhs, rhs),
            },
        }
    }

    fn eval_integer_divide(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_int(ilhs / irhs))
                                    }
                                    _ => todo!("cannot integer-divide {:?} by {:?}", lhs, rhs),
                                },
                                _ => todo!("cannot integer-divide {:?} by {:?}", lhs, rhs),
                            },
                            _ => todo!("cannot integer-divide {:?} by {:?}", lhs, rhs),
                        },
                        _ => todo!("cannot integer-divide {:?} by {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot integer-divide {:?} by {:?}", lhs, rhs),
                },
                _ => todo!("cannot integer-divide {:?} by {:?}", lhs, rhs),
            },
        }
    }

    fn eval_modulo(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_int(ilhs % irhs))
                                    }
                                    _ => todo!("cannot compute {:?} modulo {:?}", lhs, rhs),
                                },
                                _ => todo!("cannot compute {:?} modulo {:?}", lhs, rhs),
                            },
                            _ => todo!("cannot compute {:?} modulo {:?}", lhs, rhs),
                        },
                        _ => todo!("cannot compute {:?} modulo {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot compute {:?} modulo {:?}", lhs, rhs),
                },
                _ => todo!("cannot compute {:?} modulo {:?}", lhs, rhs),
            },
        }
    }

    fn eval_left_shift(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_int(ilhs << irhs))
                                    }
                                    _ => todo!("cannot compute {:?} left-shift {:?}", lhs, rhs),
                                },
                                _ => todo!("cannot compute {:?} left-shift {:?}", lhs, rhs),
                            },
                            _ => todo!("cannot compute {:?} left-shift {:?}", lhs, rhs),
                        },
                        _ => todo!("cannot compute {:?} left-shift {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot compute {:?} left-shift {:?}", lhs, rhs),
                },
                _ => todo!("cannot compute {:?} left-shift {:?}", lhs, rhs),
            },
        }
    }

    fn eval_right_shift(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_int(ilhs >> irhs))
                                    }
                                    _ => todo!("cannot compute {:?} right-shift {:?}", lhs, rhs),
                                },
                                _ => todo!("cannot compute {:?} right-shift {:?}", lhs, rhs),
                            },
                            _ => todo!("cannot compute {:?} right-shift {:?}", lhs, rhs),
                        },
                        _ => todo!("cannot compute {:?} right-shift {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot compute {:?} right-shift {:?}", lhs, rhs),
                },
                _ => todo!("cannot compute {:?} right-shift {:?}", lhs, rhs),
            },
        }
    }

    fn eval_power(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_int(ilhs.pow(*irhs as u32)))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        Ok(InternalValue::make_float((*ilhs as f64).powf(*frhs)))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        let clhs = Complex64::new(*ilhs as f64, 0.0);

                                        Ok(InternalValue::make_complex(clhs.powc(*crhs)))
                                    }
                                    _ => todo!("cannot raise {:?} to the power of {:?}", lhs, rhs),
                                },
                                ScalarValue::Float(flhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_float(flhs.powf(*irhs as f64)))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        Ok(InternalValue::make_float(flhs.powf(*frhs)))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        let clhs = Complex64::new(*flhs, 0.0);

                                        Ok(InternalValue::make_complex(clhs.powc(*crhs)))
                                    }
                                    _ => todo!("cannot raise {:?} to the power of {:?}", lhs, rhs),
                                },
                                ScalarValue::Complex(clhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        let crhs = Complex64::new(*irhs as f64, 0.0);

                                        Ok(InternalValue::make_complex(clhs.powc(crhs)))
                                    }
                                    ScalarValue::Float(frhs) => {
                                        let crhs = Complex64::new(*frhs, 0.0);

                                        Ok(InternalValue::make_complex(clhs.powc(crhs)))
                                    }
                                    ScalarValue::Complex(crhs) => {
                                        Ok(InternalValue::make_complex(clhs.powc(*crhs)))
                                    }
                                    _ => todo!("cannot add {:?} and {:?}", lhs, rhs),
                                },
                                _ => todo!("cannot raise {:?} to the power of {:?}", lhs, rhs),
                            },
                            _ => todo!("cannot raise {:?} to the power of {:?}", lhs, rhs),
                        },
                        _ => todo!("cannot raise {:?} to the power of {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot raise {:?} to the power of {:?}", lhs, rhs),
                },
                _ => todo!("cannot raise {:?} to the power of {:?}", lhs, rhs),
            },
        }
    }

    fn eval_bitwise_and(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_int(ilhs & irhs))
                                    }
                                    _ => todo!("cannot compute {:?} bit-and {:?}", lhs, rhs),
                                },
                                _ => todo!("cannot compute {:?} bit-and {:?}", lhs, rhs),
                            },
                            _ => todo!("cannot compute {:?} bit-and {:?}", lhs, rhs),
                        },
                        _ => todo!("cannot compute {:?} bit-and {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot compute {:?} bit-and {:?}", lhs, rhs),
                },
                _ => todo!("cannot compute {:?} bit-and {:?}", lhs, rhs),
            },
        }
    }

    fn eval_bitwise_or(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_int(ilhs | irhs))
                                    }
                                    _ => todo!("cannot compute {:?} bit-or {:?}", lhs, rhs),
                                },
                                _ => todo!("cannot compute {:?} bit-or {:?}", lhs, rhs),
                            },
                            _ => todo!("cannot compute {:?} bit-or {:?}", lhs, rhs),
                        },
                        _ => todo!("cannot compute {:?} bit-or {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot compute {:?} bit-or {:?}", lhs, rhs),
                },
                InternalValue::Mapping(mlhs) => match &rhs {
                    InternalValue::Mapping(mrhs) => match self.merge_dicts(mlhs, mrhs) {
                        Err(e) => Err(e),
                        Ok(v) => Ok(InternalValue::Mapping(v)),
                    },
                    _ => todo!("cannot compute {:?} bit-or {:?}", lhs, rhs),
                },
                _ => todo!("cannot compute {:?} bit-or {:?}", lhs, rhs),
            },
        }
    }

    fn eval_bitwise_xor(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.get_operands(node) {
            Err(e) => Err(e),
            Ok((lhs, rhs)) => match &lhs {
                InternalValue::Base(cvlhs) => match &rhs {
                    InternalValue::Base(cvrhs) => match &cvlhs {
                        Value::Base(svlhs) => match &cvrhs {
                            Value::Base(svrhs) => match &svlhs {
                                ScalarValue::Integer(ilhs) => match &svrhs {
                                    ScalarValue::Integer(irhs) => {
                                        Ok(InternalValue::make_int(ilhs ^ irhs))
                                    }
                                    _ => todo!("cannot compute {:?} bit-xor {:?}", lhs, rhs),
                                },
                                _ => todo!("cannot compute {:?} bit-xor {:?}", lhs, rhs),
                            },
                            _ => todo!("cannot compute {:?} bit-xor {:?}", lhs, rhs),
                        },
                        _ => todo!("cannot compute {:?} bit-xor {:?}", lhs, rhs),
                    },
                    _ => todo!("cannot compute {:?} bit-xor {:?}", lhs, rhs),
                },
                _ => todo!("cannot compute {:?} bit-xor {:?}", lhs, rhs),
            },
        }
    }

    fn eval_logical_or(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.evaluate(&node.left) {
            Err(e) => Err(e),
            Ok(v) => match &v {
                InternalValue::Base(cv) => match cv {
                    Value::Base(sv) => match sv {
                        ScalarValue::Bool(b) => {
                            if *b {
                                Ok(v)
                            } else {
                                self.evaluate(&node.right)
                            }
                        }
                        _ => Err(ConfigError::EvaluationFailed(node.start)),
                    },
                    _ => Err(ConfigError::EvaluationFailed(node.start)),
                },
                _ => Err(ConfigError::EvaluationFailed(node.start)),
            },
        }
    }

    fn eval_logical_and(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match self.evaluate(&node.left) {
            Err(e) => Err(e),
            Ok(v) => match &v {
                InternalValue::Base(cv) => match cv {
                    Value::Base(sv) => match sv {
                        ScalarValue::Bool(b) => {
                            if !*b {
                                Ok(v)
                            } else {
                                self.evaluate(&node.right)
                            }
                        }
                        _ => Err(ConfigError::EvaluationFailed(node.start)),
                    },
                    _ => Err(ConfigError::EvaluationFailed(node.start)),
                },
                _ => Err(ConfigError::EvaluationFailed(node.start)),
            },
        }
    }

    fn eval_binary(&self, node: &BinaryNode) -> StdResult<InternalValue, ConfigError> {
        match node.kind {
            TokenKind::Plus => self.eval_add(node),
            TokenKind::Minus => self.eval_subtract(node),
            TokenKind::Star => self.eval_multiply(node),
            TokenKind::Slash => self.eval_divide(node),
            TokenKind::SlashSlash => self.eval_integer_divide(node),
            TokenKind::Modulo => self.eval_modulo(node),
            TokenKind::Power => self.eval_power(node),
            TokenKind::LeftShift => self.eval_left_shift(node),
            TokenKind::RightShift => self.eval_right_shift(node),
            TokenKind::BitwiseAnd => self.eval_bitwise_and(node),
            TokenKind::BitwiseOr => self.eval_bitwise_or(node),
            TokenKind::BitwiseXor => self.eval_bitwise_xor(node),
            TokenKind::And => self.eval_logical_and(node),
            TokenKind::Or => self.eval_logical_or(node),
            _ => todo!("unhandled binary node {:?}", node.kind),
        }
    }

    fn evaluate(&self, node: &ASTValue) -> StdResult<InternalValue, ConfigError> {
        match node {
            ASTValue::TokenValue(t) => match &t.value {
                ScalarValue::Identifier(s) => match self.context {
                    None => Err(ConfigError::NoContext),
                    Some(ref cmap) => match cmap.get(s) {
                        None => Err(ConfigError::UnknownVariable(s.clone(), t.start)),
                        Some(v) => Ok(InternalValue::Base(v.clone())),
                    },
                },
                ScalarValue::String(s) => {
                    if t.kind == TokenKind::BackTick {
                        match self.convert_string(&s) {
                            None => Err(ConfigError::ConversionError(s.to_string())),
                            Some(v) => Ok(InternalValue::Base(v)),
                        }
                    } else {
                        Ok(InternalValue::Base(Value::Base(t.value.clone())))
                    }
                }
                _ => Ok(InternalValue::Base(Value::Base(t.value.clone()))),
            },
            ASTValue::Unary(un) => self.eval_unary(&un),
            ASTValue::Binary(bn) => self.eval_binary(&bn),
            ASTValue::Mapping(items) => match self.wrap_mapping(&items) {
                Err(e) => Err(e),
                Ok(data) => Ok(InternalValue::Mapping(data)),
            },
            ASTValue::List(items) => Ok(InternalValue::List(self.wrap_sequence(items))),
            _ => todo!("other AST node evaluation: {:?}", node),
        }
    }

    /// Returns ``true`` if this configuration contains the simple key ``key``
    /// (i.e. not a path), else ``false``.
    pub fn contains_key(&self, key: &str) -> bool {
        match &*self.data.borrow() {
            InternalValue::Mapping(hm) => hm.get(key).is_some(),
            _ => false,
        }
    }

    fn get_location(&self, node: &ASTValue) -> StdResult<Location, ConfigError> {
        let result = match node {
            ASTValue::TokenValue(t) => t.start,
            ASTValue::Unary(un) => un.start,
            ASTValue::Binary(bn) => bn.start,
            ASTValue::Slice(loc, _, _, _) => *loc,
            _ => panic!("unable to determine position for {:?}", node),
        };
        Ok(result)
    }

    fn get_slice_index_or_step(
        &self,
        pos: Location,
        maybe_node: &Option<ASTValue>,
    ) -> StdResult<Option<i64>, ConfigError> {
        match maybe_node {
            None => Ok(None),
            Some(node) => match self.evaluate(node) {
                Err(e) => Err(e),
                Ok(v) => match v {
                    InternalValue::Base(b) => match b {
                        Value::Base(sv) => match sv {
                            ScalarValue::Integer(i) => Ok(Some(i)),
                            _ => Err(ConfigError::InvalidPathOperand(pos)),
                        },
                        _ => Err(ConfigError::InvalidPathOperand(pos)),
                    },
                    _ => Err(ConfigError::InvalidPathOperand(pos)),
                },
            },
        }
    }

    fn get_slice(
        &self,
        pos: Location,
        list: &[Rc<RefCell<InternalValue>>],
        start: Option<i64>,
        stop: Option<i64>,
        step: Option<i64>,
    ) -> StdResult<Vec<Rc<RefCell<InternalValue>>>, ConfigError> {
        let size = list.len() as i64;
        let step_value = match step {
            None => 1,
            Some(i) => i,
        };
        if step_value == 0 {
            return Err(ConfigError::InvalidPathOperand(pos));
        }
        let mut start_index = match start {
            None => 0,
            Some(mut i) => {
                if i < 0 {
                    if i >= -size {
                        i += size;
                    } else {
                        i = 0;
                    }
                } else if i >= size {
                    i = size - 1;
                };
                i
            }
        };
        let mut stop_index = match stop {
            None => size - 1,
            Some(mut i) => {
                if i < 0 {
                    if i >= -size {
                        i += size;
                    } else {
                        i = 0;
                    }
                };
                if i > size {
                    i = size;
                }
                if step_value < 0 {
                    i += 1;
                } else {
                    i -= 1;
                }
                i
            }
        };
        if step_value < 0 && start_index < stop_index {
            std::mem::swap(&mut stop_index, &mut start_index);
        }
        let mut i = start_index;
        let mut result = vec![];
        let mut not_done = if step_value > 0 {
            i <= stop_index
        } else {
            i >= stop_index
        };
        while not_done {
            result.push(list[i as usize].clone());
            i += step_value;
            not_done = if step_value > 0 {
                i <= stop_index
            } else {
                i >= stop_index
            };
        }
        Ok(result)
    }

    fn reference_seen(&self, node: &ASTValue) -> bool {
        if let ASTValue::Unary(un) = node {
            if un.kind == TokenKind::Dollar {
                let k = (to_source(node), un.start);

                if self.refs_seen.borrow().contains(&k) {
                    return true;
                }
                self.refs_seen.borrow_mut().insert(k);
            }
        }
        false
    }

    fn get_from_path(&self, node: &ASTValue) -> StdResult<InternalValue, ConfigError> {
        let path = unpack_path(node);
        let mut result = self.data.clone();

        for element in path.iter() {
            let new_result: Rc<RefCell<InternalValue>>;

            match element {
                PathElement::Attribute(t) => {
                    let key = match t.kind {
                        TokenKind::Word => t.text.clone(),
                        TokenKind::String => match &t.value {
                            ScalarValue::String(s) => s.clone(),
                            _ => panic!("unexpected token value: {:?}", t.value),
                        },
                        _ => panic!("unexpected token kind: {:?}", t.kind),
                    };
                    match &*result.borrow() {
                        InternalValue::Base(b) => match b {
                            Value::Mapping(hm) => match hm.get(&key) {
                                None => return Err(ConfigError::NotPresent(key, Some(t.start))),
                                Some(v) => {
                                    new_result = make_node(InternalValue::Base(v.clone()));
                                }
                            },
                            Value::Config(cfg) => {
                                new_result = make_node(InternalValue::Base(cfg.get(&key)?));
                            }
                            _ => return Err(ConfigError::InvalidPathOperand(t.start)),
                        },
                        InternalValue::Mapping(hm) => {
                            match hm.get(&key) {
                                None => return Err(ConfigError::NotPresent(key, Some(t.start))),
                                Some(v) => {
                                    /*

                                    If we decide to store back the evaluated version back into the
                                    map. we need to do the stuff below. Otherwise just clone it,
                                    and evaluate later
                                    if let InternalConfigValue::AST(node) = &*v.borrow() {
                                        // check for circular references
                                        if self.reference_seen(node) {
                                            let mut locations: Vec<Location> =
                                                self.refs_seen.borrow().iter().cloned().collect();

                                            locations.sort();
                                            return Err(ConfigError::CircularReferenceError(
                                                locations,
                                            ));
                                        }
                                        // convert AST to internal config value of another type
                                        // and save it back
                                        new_result = make_node(self.evaluate(node)?)
                                    } else {
                                        new_result = v.clone();
                                    }
                                    */
                                    new_result = v.clone();
                                }
                            }
                        }
                        _ => return Err(ConfigError::InvalidPathOperand(t.start)),
                    }
                }
                PathElement::IndexedAccess(index_node) => {
                    let spos = self.get_location(index_node).unwrap();

                    match &*result.borrow() {
                        InternalValue::List(lv) => {
                            let v = self.evaluate(index_node)?;

                            match v {
                                InternalValue::Base(b) => match b {
                                    Value::Base(sv) => match sv {
                                        ScalarValue::Integer(mut index) => {
                                            let size = lv.len() as i64;

                                            if index < 0 && index >= -size {
                                                index += size;
                                            }
                                            if index < 0 || index >= size {
                                                return Err(ConfigError::IndexOutOfRange(
                                                    index, spos,
                                                ));
                                            }
                                            /*
                                             * If we decide to save an evaluated version back into
                                             * the list, we would need to do that here. Otherwise,
                                             * evaluating below (after this match) is fine.
                                             */
                                            new_result = lv[index as usize].clone();
                                        }
                                        _ => return Err(ConfigError::InvalidPathOperand(spos)),
                                    },
                                    _ => return Err(ConfigError::InvalidPathOperand(spos)),
                                },
                                _ => return Err(ConfigError::InvalidPathOperand(spos)),
                            }
                        }
                        _ => return Err(ConfigError::InvalidPathOperand(spos)),
                    };
                }
                PathElement::SliceAccess(slice) => {
                    let spos = self.get_location(slice).unwrap();

                    match &*result.borrow() {
                        InternalValue::List(lv) => match slice {
                            ASTValue::Slice(loc, start, stop, step) => {
                                let start_index = self.get_slice_index_or_step(*loc, &*start)?;
                                let stop_index = self.get_slice_index_or_step(*loc, &*stop)?;
                                let step_value = self.get_slice_index_or_step(*loc, &*step)?;
                                let slice =
                                    self.get_slice(*loc, lv, start_index, stop_index, step_value)?;

                                new_result = make_node(InternalValue::List(slice))
                            }
                            _ => {
                                return Err(ConfigError::InvalidPathOperand(spos));
                            }
                        },
                        _ => return Err(ConfigError::InvalidPathOperand(spos)),
                    }
                }
            }

            /*
             * If the result is an AST node, we evaluate it here. Note that we don't know where it
             * came from (e.g. list or mapping) so we can't save it back in the original container -
             * to do that, we have to do the evaluation in the individual branches of the match
             * above.
             */
            let mut evaluated: Option<InternalValue> = None;

            if let InternalValue::AST(node) = &*new_result.borrow() {
                if self.reference_seen(node) {
                    let mut locations: Vec<(String, Location)> =
                        self.refs_seen.borrow().iter().cloned().collect();

                    locations.sort();
                    return Err(ConfigError::CircularReferenceError(locations));
                }
                evaluated = Some(self.evaluate(node)?);
            }
            if let Some(icv) = evaluated {
                result = make_node(icv);
            } else {
                result = new_result;
            }
        }
        let r = (&*result).borrow().clone();
        Ok(r)
    }

    fn base_unwrap_list(
        &self,
        items: &[Rc<RefCell<InternalValue>>],
        unwrap_configs: bool,
    ) -> StdResult<Vec<Value>, ConfigError> {
        let mut result = vec![];

        for item in items {
            result.push(self.unwrap(&item.borrow(), unwrap_configs)?);
        }
        Ok(result)
    }

    fn unwrap_list(
        &self,
        items: &[Rc<RefCell<InternalValue>>],
        unwrap_configs: bool,
    ) -> StdResult<Value, ConfigError> {
        match self.base_unwrap_list(items, unwrap_configs) {
            Err(e) => Err(e),
            Ok(v) => Ok(Value::List(v)),
        }
    }

    fn base_unwrap_map(
        &self,
        map: &HashMap<String, Rc<RefCell<InternalValue>>>,
        unwrap_configs: bool,
    ) -> StdResult<HashMap<String, Value>, ConfigError> {
        let mut result: HashMap<String, Value> = HashMap::new();

        for (k, v) in map.iter() {
            result.insert(k.to_string(), self.unwrap(&*v.borrow(), unwrap_configs)?);
        }
        Ok(result)
    }

    fn unwrap_map(
        &self,
        map: &HashMap<String, Rc<RefCell<InternalValue>>>,
        unwrap_configs: bool,
    ) -> StdResult<Value, ConfigError> {
        match self.base_unwrap_map(map, unwrap_configs) {
            Err(e) => Err(e),
            Ok(v) => Ok(Value::Mapping(v)),
        }
    }

    fn unwrap(&self, icv: &InternalValue, unwrap_configs: bool) -> StdResult<Value, ConfigError> {
        match icv {
            InternalValue::AST(node) => match self.evaluate(&node) {
                Err(e) => Err(e),
                Ok(icv) => self.unwrap(&icv, unwrap_configs),
            },
            InternalValue::Base(cv) => match cv {
                Value::Config(c) => {
                    if !unwrap_configs {
                        Ok(cv.clone())
                    } else {
                        Ok(Value::Mapping(c.as_mapping(unwrap_configs)?))
                    }
                }
                _ => Ok(cv.clone()),
            },
            InternalValue::List(items) => self.unwrap_list(&items, unwrap_configs),
            InternalValue::Mapping(hm) => self.unwrap_map(&hm, unwrap_configs),
        }
    }

    /// Convert the configuration to a HashMap.
    ///
    /// If `unwrap_configs` is `true`, nested configurations are also converted
    /// to mappings. Otherwise, they are left as is.
    pub fn as_mapping(
        &self,
        unwrap_configs: bool,
    ) -> StdResult<HashMap<String, Value>, ConfigError> {
        let v = self.unwrap(&*self.data.borrow(), unwrap_configs)?;

        match v {
            Value::Mapping(hm) => Ok(hm),
            _ => panic!("unexpected value returned: {:?}", v),
        }
    }

    /// Returns the value for the specified configuration key.
    ///
    /// `key` can either be an identifier or a valid path.
    pub fn get(&self, key: &str) -> StdResult<Value, ConfigError> {
        self.refs_seen.borrow_mut().clear();
        match &*self.data.borrow() {
            InternalValue::Mapping(hm) => {
                if hm.is_empty() {
                    Err(ConfigError::NotLoaded)
                } else {
                    let iv = match hm.get(key) {
                        None => {
                            if is_identifier(key) {
                                Err(ConfigError::NotPresent(key.to_string(), None))
                            } else {
                                match parse_path(key) {
                                    Err(e) => Err(ConfigError::InvalidPath(e)),
                                    Ok(node) => self.get_from_path(&node),
                                }
                            }
                        }
                        Some(v) => {
                            let r = v.borrow();
                            Ok(r.clone())
                        }
                    };
                    match iv {
                        Err(e) => Err(e),
                        Ok(icv) => self.unwrap(&icv, false),
                    }
                }
            }
            _ => panic!("unexpected root data type"),
        }
    }

    pub(crate) fn convert_string(&self, s: &str) -> Option<Value> {
        (self.string_converter.0)(s, &self)
    }
}
