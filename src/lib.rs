//
//  Copyright (C) 2018-2021 Vinay Sajip.
//
/*!
A library for working with the CFG configuration format.

The CFG configuration format is a text format for configuration files which is similar to, and a
superset of, the JSON format. It dates from [2008](https://wiki.python.org/moin/HierConfig) and has
the following aims:

* Allow a hierarchical configuration scheme with support for key-value mappings and lists.
* Support cross-references between one part of the configuration and another.
* Provide the ability to compose configurations (using include and merge facilities).
* Provide the ability to access real application objects safely.

It overcomes a number of drawbacks of JSON when used as a configuration format:

* JSON is more verbose than necessary.
* JSON doesn’t allow comments.
* JSON doesn’t allow trailing commas in lists and mappings.

A simple example
================

With the following configuration file, `test0.cfg`:
```text
a: 'Hello, '
b: 'world!'
c: {
  d: 'e'
}
'f.g': 'h'
christmas_morning: `2019-12-25 08:39:49`
home: `$HOME`
foo: `$FOO|bar`
```

You can load and query the above configuration using, for example,
[the evcxr REPL](https://github.com/google/evcxr/blob/master/evcxr_repl/README.md):

```text
$ evcxr
>> :dep cfg-lib
>> use cfg_lib::*;
```

Loading a configuration
-----------------------

The configuration above can be loaded as shown below. In the REPL shell:
```text
>> let cfg = Config::from_file("test0.cfg").unwrap();
```

The successful [`from_file()`](config/struct.Config.html#method.from_file) call returns a [Config](config/struct.Config.html) instance
which can be used to query the configuration.

Access elements with keys
-------------------------
Accessing elements of the configuration with a simple key is not much harder than using a HashMap:
```text
>> cfg.get("a")
Ok(Base(String("Hello, ")))
>> cfg.get("b")
Ok(Base(String("world!")))
```
The values returned are of type [Value](config/enum.Value.html).

Access elements with paths
--------------------------
As well as simple keys, elements can also be accessed using path strings:
```text
>> cfg.get("c.d")
Ok(Base(String("e")))
```
Here, the desired value is obtained in a single step, by (under the hood) walking the path `c.d` –
first getting the mapping at key c, and then the value at d in the resulting mapping.

Note that you can have simple keys which look like paths:
```text
>> cfg.get("f.g")
Ok(Base(String("h")))
```
If a key is given that exists in the configuration, it is used as such, and if it is not present in
the configuration, an attempt is made to interpret it as a path. Thus, f.g is present and accessed
via key, whereas c.d is not an existing key, so is interpreted as a path.

Access to date/time objects
---------------------------
You can also get native Rust date/time objects from a configuration, by using an ISO date/time
pattern in a backtick-string:
```text
>> cfg.get("christmas_morning")
Ok(Base(DateTime(2019-12-25T08:39:49+00:00)))
```
You get either NaiveDate objects, if you specify the date part only, or else DateTime<FixedOffset>
objects, if you specify a time component as well. If no offset is specified, it is assumed to be
zero.

Access to environment variables
-------------------------------
To access an environment variable, use a backtick-string of the form `$VARNAME`:
```text
>> cfg.get("home")
Ok(Base(String("/home/vinay")))
```
You can specify a default value to be used if an environment variable isn’t present using the
`$VARNAME|default-value` form. Whatever string follows the pipe character (including the empty
string) is returned if the VARNAME is not a variable in the environment.
```text
>> cfg.get("foo")
Ok(Base(String("bar")))
```

For more information, see [the CFG documentation](https://docs.red-dove.com/cfg/index.html).

*/

#![deny(missing_docs)]

pub mod config;

pub use config::*;

#[macro_use]
extern crate log;

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::env;
    use std::fs::{canonicalize, File};
    use std::io::{BufRead, BufReader, Cursor};
    use std::path::{self};
    use std::result::Result;

    use chrono::{DateTime, FixedOffset, NaiveDate, NaiveDateTime, NaiveTime};
    use lazy_static::lazy_static;
    use num_complex::Complex64;
    use regex::Regex;

    use crate::config::*;

    lazy_static! {
        static ref SEPARATOR_PATTERN: Regex =
            Regex::new(r"^-- ([A-Z]\d+) -+").expect("couldn't compile regex");
        static ref PATH_SEP_STRING: String = path::MAIN_SEPARATOR.to_string();
    }

    fn data_file_path(parts: &[&str]) -> String {
        let mut v = Vec::new();

        v.push("resources");
        v.extend_from_slice(parts);
        let s = v.join(&PATH_SEP_STRING);

        String::from(s)
    }

    fn load_data(file_name: String) -> HashMap<String, String> {
        let mut result = HashMap::new();
        let f = File::open(file_name).expect("Couldn't open the file");
        let mut key = String::new();
        let mut lines: Vec<String> = vec![];

        for line in BufReader::new(f).lines() {
            match line {
                Err(e) => {
                    panic!("Failed to read: {}", e);
                }
                Ok(s) => match SEPARATOR_PATTERN.captures(&s) {
                    None => {
                        lines.push(String::from(s.clone()));
                    }
                    Some(c) => {
                        if key.len() > 0 && lines.len() > 0 {
                            result.insert(key, lines.join("\n"));
                        }
                        match c.get(0) {
                            None => {
                                panic!("A match was expected");
                            }
                            Some(m) => {
                                key = String::from(m.as_str());
                            }
                        }
                        lines.clear();
                    }
                },
            }
        }
        return result;
    }

    macro_rules! loc {
        ($line:expr, $column:expr) => {{
            Location {
                line: $line,
                column: $column,
            }
        }};
    }

    macro_rules! assert_loc {
        ($loc:expr, $line:expr, $column:expr) => {{
            assert_eq!($line, $loc.line);
            assert_eq!($column, $loc.column);
        }};
    }

    #[test]
    fn location() {
        let mut loc = loc!(1, 1);
        let loc2 = loc!(2, 7);

        assert_loc!(loc, 1, 1);

        loc.next_line();
        assert_loc!(loc, 2, 1);

        assert_loc!(loc2, 2, 7);

        let loc3 = loc2.clone();

        assert_loc!(loc3, 2, 7);

        loc.update(&loc3);
        assert_loc!(loc, 2, 7);
    }

    #[test]
    fn decoding() {
        let p = data_file_path(&["all_unicode.bin"]);
        let f = File::open(p).expect("Couldn't open all_unicode.bin");
        let mut decoder = Decoder::new(f);

        fn check(i: u32, offset: usize, result: DecodeResult) {
            match result {
                DecodeResult::EOF => {
                    panic!("EOF unexpected at {:06x}", offset);
                }
                DecodeResult::Error(e) => panic!("Failed at {:06x}: {:?}", offset, e),
                DecodeResult::Char(c, the_bytes) => {
                    assert_eq!(
                        i,
                        c as u32,
                        "Failed at {}, bytes {:?}, file offset {:06x}",
                        i,
                        the_bytes,
                        offset - the_bytes.len()
                    );
                }
            }
        }

        for i in 0..0xD800 {
            let result = decoder.decode(/* &mut log */);
            let offset = decoder.bytes_read;

            check(i, offset, result);
        }

        for i in 0xE000..0x110000 {
            let result = decoder.decode(/* &mut log */);
            let offset = decoder.bytes_read;

            check(i, offset, result);
        }
    }

    #[test]
    fn decoding_edge_cases() {
        let mut d = Decoder::new(Box::new("".as_bytes()));

        match d.decode() {
            DecodeResult::EOF => {}
            _ => panic!("unexpected result"),
        }
        d = Decoder::new(Box::new(Cursor::new([195u8])));
        //d.enable_logging(true);
        match d.decode() {
            DecodeResult::Error(e) => match e {
                DecoderError::InvalidBytes(invalid) => {
                    assert_eq!(vec![195u8], invalid);
                }
                v => panic!("decoder error expected, {:?} seen", v),
            },
            v => panic!("error expected, {:?} seen", v),
        }
        d = Decoder::new(Box::new(Cursor::new([0u8])));
        match d.decode() {
            DecodeResult::Char(c, valid) => {
                assert_eq!('\0', c);
                assert_eq!(vec![0u8], valid);
            }
            v => panic!("char expected, {:?} seen", v),
        }
    }

    #[test]
    fn from_data() {
        let p = data_file_path(&["testdata.txt"]);
        //let file_name = String::from("testdata.txt");
        let mapping = load_data(p);

        for (_key, _value) in &mapping {
            let _tokenizer = Tokenizer::new(Box::new(_value.as_bytes()));
        }
    }

    type LocationTuple = (u16, u16);

    #[test]
    fn tokenizing() {
        fn build_ok_case(
            source: &str,
            kind: TokenKind,
            value: ScalarValue,
            start: LocationTuple,
            end: LocationTuple,
        ) -> (&str, Result<Token, RecognizerError>) {
            let s = loc!(start.0, start.1);
            let e = loc!(end.0, end.1);

            (
                source,
                Ok(Token {
                    kind,
                    text: source.trim_start_matches(' ').to_string(),
                    value,
                    start: s,
                    end: e,
                }),
            )
        }

        let cases = vec![
            build_ok_case("", TokenKind::EOF, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case(
                "# a comment",
                TokenKind::Newline,
                ScalarValue::None,
                (1, 1),
                (1, 12),
            ),
            build_ok_case("\n", TokenKind::Newline, ScalarValue::None, (1, 1), (2, 0)),
            build_ok_case(
                " foo",
                TokenKind::Word,
                ScalarValue::Identifier("foo".to_string()),
                (1, 2),
                (1, 4),
            ),
            build_ok_case(
                "true",
                TokenKind::True,
                ScalarValue::Bool(true),
                (1, 1),
                (1, 4),
            ),
            build_ok_case(
                "false",
                TokenKind::False,
                ScalarValue::Bool(false),
                (1, 1),
                (1, 5),
            ),
            build_ok_case("null", TokenKind::None, ScalarValue::Null, (1, 1), (1, 4)),
            build_ok_case("is", TokenKind::Is, ScalarValue::None, (1, 1), (1, 2)),
            build_ok_case("in", TokenKind::In, ScalarValue::None, (1, 1), (1, 2)),
            build_ok_case("not", TokenKind::Not, ScalarValue::None, (1, 1), (1, 3)),
            build_ok_case("and", TokenKind::And, ScalarValue::None, (1, 1), (1, 3)),
            build_ok_case("or", TokenKind::Or, ScalarValue::None, (1, 1), (1, 2)),
            ("'", Err(RecognizerError::UnterminatedString(loc!(1, 1)))),
            ("'''", Err(RecognizerError::UnterminatedString(loc!(1, 3)))),
            build_ok_case(
                "''",
                TokenKind::String,
                ScalarValue::String("".to_string()),
                (1, 1),
                (1, 2),
            ),
            build_ok_case(
                "''''''",
                TokenKind::String,
                ScalarValue::String("".to_string()),
                (1, 1),
                (1, 6),
            ),
            build_ok_case(
                "'foo'",
                TokenKind::String,
                ScalarValue::String("foo".to_string()),
                (1, 1),
                (1, 5),
            ),
            build_ok_case(
                "'''bar'''",
                TokenKind::String,
                ScalarValue::String("bar".to_string()),
                (1, 1),
                (1, 9),
            ),
            build_ok_case(
                "`bar`",
                TokenKind::BackTick,
                ScalarValue::String("bar".to_string()),
                (1, 1),
                (1, 5),
            ),
            ("'foo", Err(RecognizerError::UnterminatedString(loc!(1, 4)))),
            (
                "'''bar''",
                Err(RecognizerError::UnterminatedString(loc!(1, 8))),
            ),
            (
                "'''bar'",
                Err(RecognizerError::UnterminatedString(loc!(1, 7))),
            ),
            ("`foo", Err(RecognizerError::UnterminatedString(loc!(1, 4)))),
            ("`foo\n", Err(RecognizerError::InvalidString(loc!(1, 5)))),
            ("`foo\r\n", Err(RecognizerError::InvalidString(loc!(1, 5)))),
            (
                "'abc\\\ndef",
                Err(RecognizerError::UnterminatedString(loc!(2, 3))),
            ),
            (
                "\\ ",
                Err(RecognizerError::UnexpectedCharacter(' ', loc!(1, 2))),
            ),
            build_ok_case(
                "\"\"",
                TokenKind::String,
                ScalarValue::String("".to_string()),
                (1, 1),
                (1, 2),
            ),
            build_ok_case(
                "4",
                TokenKind::Number,
                ScalarValue::Integer(4i64),
                (1, 1),
                (1, 1),
            ),
            build_ok_case(
                "2.71828",
                TokenKind::Number,
                ScalarValue::Float(2.71828),
                (1, 1),
                (1, 7),
            ),
            build_ok_case(
                ".5",
                TokenKind::Number,
                ScalarValue::Float(0.5),
                (1, 1),
                (1, 2),
            ),
            build_ok_case(
                "-.5",
                TokenKind::Number,
                ScalarValue::Float(-0.5),
                (1, 1),
                (1, 3),
            ),
            build_ok_case(
                "0x123aBc",
                TokenKind::Number,
                ScalarValue::Integer(0x123abci64),
                (1, 1),
                (1, 8),
            ),
            build_ok_case(
                "0o123",
                TokenKind::Number,
                ScalarValue::Integer(83i64),
                (1, 1),
                (1, 5),
            ),
            build_ok_case(
                "0123",
                TokenKind::Number,
                ScalarValue::Integer(83i64),
                (1, 1),
                (1, 4),
            ),
            build_ok_case(
                "0b000101100111",
                TokenKind::Number,
                ScalarValue::Integer(0x167i64),
                (1, 1),
                (1, 14),
            ),
            build_ok_case(
                "0b00_01_0110_0111",
                TokenKind::Number,
                ScalarValue::Integer(0x167i64),
                (1, 1),
                (1, 17),
            ),
            build_ok_case(
                "1e8",
                TokenKind::Number,
                ScalarValue::Float(1e8),
                (1, 1),
                (1, 3),
            ),
            build_ok_case(
                "1e-8",
                TokenKind::Number,
                ScalarValue::Float(1e-8),
                (1, 1),
                (1, 4),
            ),
            ("9a", Err(RecognizerError::InvalidNumber(loc!(1, 2)))),
            ("079", Err(RecognizerError::InvalidNumber(loc!(1, 1)))),
            ("0xaBcZ", Err(RecognizerError::InvalidNumber(loc!(1, 6)))),
            ("0.5.7", Err(RecognizerError::InvalidNumber(loc!(1, 4)))),
            (".5z", Err(RecognizerError::InvalidNumber(loc!(1, 3)))),
            ("0o79", Err(RecognizerError::InvalidNumber(loc!(1, 4)))),
            (" 0.4e-z", Err(RecognizerError::InvalidNumber(loc!(1, 7)))),
            (" 0.4e-8.3", Err(RecognizerError::InvalidNumber(loc!(1, 8)))),
            ("4e-8.3", Err(RecognizerError::InvalidNumber(loc!(1, 5)))),
            (" 089z", Err(RecognizerError::InvalidNumber(loc!(1, 5)))),
            ("0o89z", Err(RecognizerError::InvalidNumber(loc!(1, 3)))),
            ("0X89g", Err(RecognizerError::InvalidNumber(loc!(1, 5)))),
            ("10z", Err(RecognizerError::InvalidNumber(loc!(1, 3)))),
            ("0.4e-8Z", Err(RecognizerError::InvalidNumber(loc!(1, 7)))),
            ("123_", Err(RecognizerError::InvalidNumber(loc!(1, 4)))),
            ("1__23", Err(RecognizerError::InvalidNumber(loc!(1, 3)))),
            ("1_2__3", Err(RecognizerError::InvalidNumber(loc!(1, 5)))),
            ("0.4e-8_", Err(RecognizerError::InvalidNumber(loc!(1, 7)))),
            ("0.4_e-8", Err(RecognizerError::InvalidNumber(loc!(1, 5)))),
            ("0._4e-8", Err(RecognizerError::InvalidNumber(loc!(1, 3)))),
            build_ok_case(":", TokenKind::Colon, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case("-", TokenKind::Minus, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case("+", TokenKind::Plus, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case("*", TokenKind::Star, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case("**", TokenKind::Power, ScalarValue::None, (1, 1), (1, 2)),
            build_ok_case("/", TokenKind::Slash, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case(
                "//",
                TokenKind::SlashSlash,
                ScalarValue::None,
                (1, 1),
                (1, 2),
            ),
            build_ok_case("%", TokenKind::Modulo, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case(",", TokenKind::Comma, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case("{", TokenKind::LeftCurly, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case(
                "}",
                TokenKind::RightCurly,
                ScalarValue::None,
                (1, 1),
                (1, 1),
            ),
            build_ok_case(
                "[",
                TokenKind::LeftBracket,
                ScalarValue::None,
                (1, 1),
                (1, 1),
            ),
            build_ok_case(
                "]",
                TokenKind::RightBracket,
                ScalarValue::None,
                (1, 1),
                (1, 1),
            ),
            build_ok_case(
                "(",
                TokenKind::LeftParenthesis,
                ScalarValue::None,
                (1, 1),
                (1, 1),
            ),
            build_ok_case(
                ")",
                TokenKind::RightParenthesis,
                ScalarValue::None,
                (1, 1),
                (1, 1),
            ),
            build_ok_case("@", TokenKind::At, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case("$", TokenKind::Dollar, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case("<", TokenKind::LessThan, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case(
                "<=",
                TokenKind::LessThanOrEqual,
                ScalarValue::None,
                (1, 1),
                (1, 2),
            ),
            build_ok_case(
                "<>",
                TokenKind::AltUnequal,
                ScalarValue::None,
                (1, 1),
                (1, 2),
            ),
            build_ok_case(
                "<<",
                TokenKind::LeftShift,
                ScalarValue::None,
                (1, 1),
                (1, 2),
            ),
            build_ok_case(
                ">",
                TokenKind::GreaterThan,
                ScalarValue::None,
                (1, 1),
                (1, 1),
            ),
            build_ok_case(
                ">=",
                TokenKind::GreaterThanOrEqual,
                ScalarValue::None,
                (1, 1),
                (1, 2),
            ),
            build_ok_case(
                ">>",
                TokenKind::RightShift,
                ScalarValue::None,
                (1, 1),
                (1, 2),
            ),
            build_ok_case("!", TokenKind::Not, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case("!=", TokenKind::Unequal, ScalarValue::None, (1, 1), (1, 2)),
            build_ok_case(
                "~",
                TokenKind::BitwiseComplement,
                ScalarValue::None,
                (1, 1),
                (1, 1),
            ),
            build_ok_case(
                "&",
                TokenKind::BitwiseAnd,
                ScalarValue::None,
                (1, 1),
                (1, 1),
            ),
            build_ok_case("|", TokenKind::BitwiseOr, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case(
                "^",
                TokenKind::BitwiseXor,
                ScalarValue::None,
                (1, 1),
                (1, 1),
            ),
            build_ok_case(".", TokenKind::Dot, ScalarValue::None, (1, 1), (1, 1)),
            build_ok_case("==", TokenKind::Equal, ScalarValue::None, (1, 1), (1, 2)),
            (
                ";",
                Err(RecognizerError::UnexpectedCharacter(';', loc!(1, 1))),
            ),
        ];

        for case in cases {
            let c = Cursor::new(case.0);
            let mut tokenizer = Tokenizer::new(Box::new(c));

            let token = tokenizer.get_token();
            let expected = case.1;

            //println!("case: {}", case.0);
            match expected {
                Ok(e) => {
                    let msg = format!("failed for {}", case.0);

                    let t = token.expect("a token was expected");
                    assert_eq!(t.kind, e.kind, "{}", msg);
                    assert_eq!(t.text, e.text, "{}", msg);
                    assert_eq!(t.start, e.start, "{}", msg);
                    assert_eq!(t.end, e.end, "{}", msg);
                }
                Err(e) => {
                    let te = token.err().expect("an error was expected");
                    assert_eq!(te, e);
                }
            }
        }
    }

    #[test]
    fn escapes() {
        let cases = vec![
            ("'\\a'", "\u{0007}"),
            ("'\\b'", "\u{0008}"),
            ("'\\f'", "\u{000C}"),
            ("'\\n'", "\n"),
            ("'\\r'", "\r"),
            ("'\\t'", "\t"),
            ("'\\v'", "\u{000B}"),
            ("'\\\\'", "\\"),
            ("'\\\\'", "\\"),
            ("'\\''", "'"),
            ("'\\\"'", "\""),
            ("'\\xAB'", "\u{00AB}"),
            ("'\\u2803'", "\u{2803}"),
            ("'\\u2803'", "\u{2803}"),
            ("'\\u28A0abc\\u28a0'", "\u{28A0}abc\u{28A0}"),
            ("'\\u28A0abc'", "\u{28A0}abc"),
            ("'\\U0010ffff'", "\u{10FFFF}"),
        ];

        for (s, e) in cases {
            let c = Cursor::new(s);
            let mut tokenizer = Tokenizer::new(Box::new(c));
            let token = tokenizer.get_token().expect("a token was expected");

            match token.value {
                ScalarValue::String(s) => {
                    assert_eq!(e.to_string(), s);
                }
                v => panic!("unexpected token value: {:?}", v),
            }
        }

        let bad_cases = vec![
            "'\\z'",
            "'\\x'",
            "'\\xa'",
            "'\\xaz'",
            "'\\u'",
            "'\\u0'",
            "'\\u01'",
            "'\\u012'",
            "'\\u012z'",
            "'\\u012zA'",
            "'\\ud800'",
            "'\\udfff'",
            "'\\U00110000'",
        ];

        for s in bad_cases {
            let c = Cursor::new(s);
            let mut tokenizer = Tokenizer::new(Box::new(c));
            let e = tokenizer.get_token().err().expect("an error was expected");

            match e {
                RecognizerError::InvalidEscapeSequence(_, _) => {}
                v => panic!("unexpected error value: {:?}", v),
            }
        }
    }

    #[test]
    fn locations() {
        let mut positions: Vec<Vec<u16>> = vec![];
        let mut p = data_file_path(&["pos.forms.cfg.txt"]);
        let mut f = File::open(&p).expect("Couldn't open pos.forms.cfg");

        fn to_int(s: &str) -> u16 {
            u16::from_str_radix(s, 10).expect("couldn't parse string to integer")
        }

        for line in BufReader::new(f).lines() {
            let p = line
                .expect("a line was expected")
                .split(' ')
                .map(to_int)
                .collect::<Vec<u16>>();

            assert_eq!(4, p.len());
            positions.push(p);
        }
        p = data_file_path(&["forms.cfg"]);
        f = File::open(&p).expect("Couldn't open forms.cfg");

        let mut tokenizer = Tokenizer::new(Box::new(f));

        for (_, p) in positions.iter().enumerate() {
            let t = tokenizer.get_token().expect("a token was expected");
            let s = loc!(p[0], p[1]);
            let e = loc!(p[2], p[3]);

            assert_eq!(s, t.start);
            assert_eq!(e, t.end);
        }
    }

    #[test]
    fn strings() {
        let c = Cursor::new("'foo' \"bar\" 'baz'");
        let mut parser = Parser::new(Box::new(c)).expect("unable to create parser");
        let t = parser.strings().expect("a token was expected");

        assert_eq!(t.kind, TokenKind::String);
        match t.value {
            ScalarValue::String(s) => assert_eq!(s, "foobarbaz"),
            e => panic!("unexpected result: {:?}", e),
        }
        assert_loc!(t.start, 1, 1);
        assert_loc!(t.end, 1, 17);
    }

    fn build_token(kind: TokenKind, source: &str, value: ScalarValue, scol: u16) -> Token {
        let src = source.to_string();
        let ecol: u16 = (src.len() as u16) - 1 + scol;
        let s = loc!(1, scol);
        let e = loc!(1, ecol);
        Token {
            kind,
            text: source.to_string(),
            value,
            start: s,
            end: e,
        }
    }

    fn build_identifier(source: &str, scol: u16) -> Token {
        build_token(
            TokenKind::Word,
            source,
            ScalarValue::Identifier(source.to_string()),
            scol,
        )
    }

    fn build_string(source: &str, v: &str, scol: u16) -> Token {
        build_token(
            TokenKind::String,
            source,
            ScalarValue::String(v.to_string()),
            scol,
        )
    }

    fn build_integer(source: &str, i: i64, scol: u16) -> Token {
        build_token(TokenKind::Number, source, ScalarValue::Integer(i), scol)
    }

    fn build_float(source: &str, fv: f64, scol: u16) -> Token {
        let v = ScalarValue::Float(fv);

        build_token(TokenKind::Number, source, v, scol)
    }

    fn build_complex(source: &str, re: f64, im: f64, scol: u16) -> Token {
        let v = ScalarValue::Complex(Complex64::new(re, im));

        build_token(TokenKind::Complex, source, v, scol)
    }

    fn build_scalar(source: &str, scol: u16) -> Token {
        let kind;
        let value;

        if source.eq("true") {
            kind = TokenKind::True;
            value = ScalarValue::Bool(true);
        } else if source.eq("false") {
            kind = TokenKind::False;
            value = ScalarValue::Bool(false);
        } else {
            kind = TokenKind::None;
            value = ScalarValue::Null;
        }
        build_token(kind, source, value, scol)
    }

    #[test]
    fn values() {
        let cases = vec![
            ("foo", Ok(build_identifier("foo", 1))),
            ("'foo'", Ok(build_string("'foo'", "foo", 1))),
            ("4", Ok(build_integer("4", 4i64, 1))),
            ("3.14159", Ok(build_float("3.14159", 3.14159f64, 1))),
            ("2j", Ok(build_complex("2j", 0.0f64, 2.0f64, 1))),
            ("null", Ok(build_scalar("null", 1))),
            ("true", Ok(build_scalar("true", 1))),
            ("false", Ok(build_scalar("false", 1))),
            ("-4", Ok(build_integer("-4", -4i64, 1))),
            ("1234", Ok(build_integer("1234", 1234i64, 1))),
            ("1234_5678", Ok(build_integer("1234_5678", 12345678i64, 1))),
            (
                "123_456_789",
                Ok(build_integer("123_456_789", 123456789i64, 1)),
            ),
        ];

        for case in cases {
            let c = Cursor::new(case.0);
            let mut parser = Parser::new(Box::new(c)).expect("unable to create parser");
            let value = parser.value();
            let expected = case.1;

            match expected {
                Ok(e) => {
                    let v = value.expect("a value was expected");
                    assert_eq!(v, e);
                }
                Err(e) => {
                    let ve = value.err().expect("an error was expected");
                    assert_eq!(ve, e);
                }
            }
        }
    }

    #[test]
    fn atoms() {
        let cases = vec![
            ("foo", Ok(ASTValue::TokenValue(build_identifier("foo", 1)))),
            (
                "'foo'",
                Ok(ASTValue::TokenValue(build_string("'foo'", "foo", 1))),
            ),
            ("4", Ok(ASTValue::TokenValue(build_integer("4", 4i64, 1)))),
            (
                "3.14159",
                Ok(ASTValue::TokenValue(build_float("3.14159", 3.14159f64, 1))),
            ),
            (
                "2j",
                Ok(ASTValue::TokenValue(build_complex("2j", 0.0, 2.0f64, 1))),
            ),
            ("null", Ok(ASTValue::TokenValue(build_scalar("null", 1)))),
            ("true", Ok(ASTValue::TokenValue(build_scalar("true", 1)))),
            ("false", Ok(ASTValue::TokenValue(build_scalar("false", 1)))),
            (
                "-4",
                Ok(ASTValue::TokenValue(build_integer("-4", -4i64, 1))),
            ),
        ];

        for case in cases {
            let c = Cursor::new(case.0);
            let mut parser = Parser::new(Box::new(c)).expect("unable to create parser");
            let atom = parser.atom();
            let expected = case.1;

            match expected {
                Ok(e) => {
                    let a = atom.expect("an atom was expected");
                    assert_eq!(a, e);
                }
                Err(e) => {
                    let ae = atom.err().expect("an error was expected");
                    assert_eq!(ae, e);
                }
            }
        }
    }

    #[test]
    fn primaries() {
        let cases = vec![
            (
                "a.b",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Dot,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::TokenValue(build_identifier("b", 3))),
                    start: loc!(1, 2),
                })),
            ),
            (
                "a[1:2]",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Colon,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::Slice(
                        loc!(1, 3),
                        Box::new(Some(ASTValue::TokenValue(build_integer("1", 1i64, 3)))),
                        Box::new(Some(ASTValue::TokenValue(build_integer("2", 2i64, 5)))),
                        Box::new(None),
                    )),
                    start: loc!(1, 2),
                })),
            ),
            (
                "foo[start:stop:step]",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Colon,
                    left: Box::new(ASTValue::TokenValue(build_identifier("foo", 1))),
                    right: Box::new(ASTValue::Slice(
                        loc!(1, 5),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("start", 5)))),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("stop", 11)))),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("step", 16)))),
                    )),
                    start: loc!(1, 4),
                })),
            ),
            (
                "foo[start:stop]",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Colon,
                    left: Box::new(ASTValue::TokenValue(build_identifier("foo", 1))),
                    right: Box::new(ASTValue::Slice(
                        loc!(1, 5),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("start", 5)))),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("stop", 11)))),
                        Box::new(None),
                    )),
                    start: loc!(1, 4),
                })),
            ),
            (
                "foo[start:stop:]",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Colon,
                    left: Box::new(ASTValue::TokenValue(build_identifier("foo", 1))),
                    right: Box::new(ASTValue::Slice(
                        loc!(1, 5),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("start", 5)))),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("stop", 11)))),
                        Box::new(None),
                    )),
                    start: loc!(1, 4),
                })),
            ),
            (
                "foo[start:]",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Colon,
                    left: Box::new(ASTValue::TokenValue(build_identifier("foo", 1))),
                    right: Box::new(ASTValue::Slice(
                        loc!(1, 5),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("start", 5)))),
                        Box::new(None),
                        Box::new(None),
                    )),
                    start: loc!(1, 4),
                })),
            ),
            (
                "foo[start::]",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Colon,
                    left: Box::new(ASTValue::TokenValue(build_identifier("foo", 1))),
                    right: Box::new(ASTValue::Slice(
                        loc!(1, 5),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("start", 5)))),
                        Box::new(None),
                        Box::new(None),
                    )),
                    start: loc!(1, 4),
                })),
            ),
            (
                "foo[:stop]",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Colon,
                    left: Box::new(ASTValue::TokenValue(build_identifier("foo", 1))),
                    right: Box::new(ASTValue::Slice(
                        loc!(1, 5),
                        Box::new(None),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("stop", 6)))),
                        Box::new(None),
                    )),
                    start: loc!(1, 4),
                })),
            ),
            (
                "foo[:stop:]",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Colon,
                    left: Box::new(ASTValue::TokenValue(build_identifier("foo", 1))),
                    right: Box::new(ASTValue::Slice(
                        loc!(1, 5),
                        Box::new(None),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("stop", 6)))),
                        Box::new(None),
                    )),
                    start: loc!(1, 4),
                })),
            ),
            (
                "foo[::step]",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Colon,
                    left: Box::new(ASTValue::TokenValue(build_identifier("foo", 1))),
                    right: Box::new(ASTValue::Slice(
                        loc!(1, 5),
                        Box::new(None),
                        Box::new(None),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("step", 7)))),
                    )),
                    start: loc!(1, 4),
                })),
            ),
            (
                "foo[::]",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Colon,
                    left: Box::new(ASTValue::TokenValue(build_identifier("foo", 1))),
                    right: Box::new(ASTValue::Slice(
                        loc!(1, 5),
                        Box::new(None),
                        Box::new(None),
                        Box::new(None),
                    )),
                    start: loc!(1, 4),
                })),
            ),
            (
                "foo[start::step]",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Colon,
                    left: Box::new(ASTValue::TokenValue(build_identifier("foo", 1))),
                    right: Box::new(ASTValue::Slice(
                        loc!(1, 5),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("start", 5)))),
                        Box::new(None),
                        Box::new(Some(ASTValue::TokenValue(build_identifier("step", 12)))),
                    )),
                    start: loc!(1, 4),
                })),
            ),
            (
                "foo[start::step:]",
                Err(RecognizerError::UnexpectedToken(
                    token_text(TokenKind::RightBracket),
                    token_text(TokenKind::Colon),
                    loc!(1, 16),
                )),
            ),
            (
                "[1, 2]",
                Ok(ASTValue::List(vec![
                    ASTValue::TokenValue(build_integer("1", 1i64, 2)),
                    ASTValue::TokenValue(build_integer("2", 2i64, 5)),
                ])),
            ),
            (
                "{a: b, c: d}",
                Ok(ASTValue::Mapping(vec![
                    (
                        Token {
                            kind: TokenKind::Word,
                            text: "a".to_string(),
                            value: ScalarValue::Identifier("a".to_string()),
                            start: loc!(1, 2),
                            end: loc!(1, 2),
                        },
                        ASTValue::TokenValue(build_identifier("b", 5)),
                    ),
                    (
                        Token {
                            kind: TokenKind::Word,
                            text: "c".to_string(),
                            value: ScalarValue::Identifier("c".to_string()),
                            start: loc!(1, 8),
                            end: loc!(1, 8),
                        },
                        ASTValue::TokenValue(build_identifier("d", 11)),
                    ),
                ])),
            ),
            (
                "-4",
                Ok(ASTValue::TokenValue(build_integer("-4", -4i64, 1))),
            ),
        ];

        for case in cases {
            let c = Cursor::new(case.0);
            let mut parser = Parser::new(Box::new(c)).expect("unable to create parser");
            let primary = parser.primary();
            let expected = case.1;

            match expected {
                Ok(e) => {
                    let p = primary.expect("a primary was expected");
                    assert_eq!(p, e, "failed for {}", case.0);
                }
                Err(e) => {
                    let pe = primary.err().expect("an error was expected");
                    assert_eq!(pe, e, "failed for {}", case.0);
                }
            }
        }
    }

    #[test]
    fn exprs() {
        let cases = vec![
            (
                "a or b || c",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Or,
                    left: Box::new(ASTValue::Binary(BinaryNode {
                        kind: TokenKind::Or,
                        left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                        right: Box::new(ASTValue::TokenValue(build_identifier("b", 6))),
                        start: loc!(1, 3),
                    })),
                    right: Box::new(ASTValue::TokenValue(build_identifier("c", 11))),
                    start: loc!(1, 8),
                })),
            ),
            (
                "a and b && c",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::And,
                    left: Box::new(ASTValue::Binary(BinaryNode {
                        kind: TokenKind::And,
                        left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                        right: Box::new(ASTValue::TokenValue(build_identifier("b", 7))),
                        start: loc!(1, 3),
                    })),
                    right: Box::new(ASTValue::TokenValue(build_identifier("c", 12))),
                    start: loc!(1, 9),
                })),
            ),
            (
                "not a",
                Ok(ASTValue::Unary(UnaryNode {
                    kind: TokenKind::Not,
                    operand: Box::new(ASTValue::TokenValue(build_identifier("a", 5))),
                    start: loc!(1, 1),
                })),
            ),
            (
                "not ! a",
                Ok(ASTValue::Unary(UnaryNode {
                    kind: TokenKind::Not,
                    operand: Box::new(ASTValue::Unary(UnaryNode {
                        kind: TokenKind::Not,
                        operand: Box::new(ASTValue::TokenValue(build_identifier("a", 7))),
                        start: loc!(1, 5),
                    })),
                    start: loc!(1, 1),
                })),
            ),
            (
                "a < b",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::LessThan,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::TokenValue(build_identifier("b", 5))),
                    start: loc!(1, 3),
                })),
            ),
            (
                "a is not b",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::IsNot,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::TokenValue(build_identifier("b", 10))),
                    start: loc!(1, 3),
                })),
            ),
            (
                "a not in b",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::NotIn,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::TokenValue(build_identifier("b", 10))),
                    start: loc!(1, 3),
                })),
            ),
            (
                "a | b",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::BitwiseOr,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::TokenValue(build_identifier("b", 5))),
                    start: loc!(1, 3),
                })),
            ),
            (
                "a ^ b",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::BitwiseXor,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::TokenValue(build_identifier("b", 5))),
                    start: loc!(1, 3),
                })),
            ),
            (
                "a & b",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::BitwiseAnd,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::TokenValue(build_identifier("b", 5))),
                    start: loc!(1, 3),
                })),
            ),
            (
                "a << b",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::LeftShift,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::TokenValue(build_identifier("b", 6))),
                    start: loc!(1, 3),
                })),
            ),
            (
                "a + b",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Plus,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::TokenValue(build_identifier("b", 5))),
                    start: loc!(1, 3),
                })),
            ),
            (
                "a // b",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::SlashSlash,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::TokenValue(build_identifier("b", 6))),
                    start: loc!(1, 3),
                })),
            ),
            (
                "-a",
                Ok(ASTValue::Unary(UnaryNode {
                    kind: TokenKind::Minus,
                    operand: Box::new(ASTValue::TokenValue(build_identifier("a", 2))),
                    start: loc!(1, 1),
                })),
            ),
            (
                "a ** b",
                Ok(ASTValue::Binary(BinaryNode {
                    kind: TokenKind::Power,
                    left: Box::new(ASTValue::TokenValue(build_identifier("a", 1))),
                    right: Box::new(ASTValue::TokenValue(build_identifier("b", 6))),
                    start: loc!(1, 3),
                })),
            ),
        ];

        for case in cases {
            let c = Cursor::new(case.0);
            let mut parser = Parser::new(Box::new(c)).expect("unable to create parser");
            let expr = parser.expr();
            let expected = case.1;

            match expected {
                Ok(e) => {
                    let ee = expr.expect("an expression was expected");
                    assert_eq!(ee, e, "failed for {}", case.0);
                    assert!(parser.at_end()); // should have exhausted input looking for more clauses
                }
                Err(e) => {
                    let ee = expr.err().expect("an error was expected");
                    assert_eq!(ee, e, "failed for {}", case.0);
                }
            }
        }
    }

    fn make_map(av: ASTValue) -> HashMap<String, ASTValue> {
        let mut result = HashMap::new();

        match av {
            ASTValue::Mapping(kvps) => {
                for (t, v) in kvps {
                    let k;

                    assert!(t.kind == TokenKind::String || t.kind == TokenKind::Word);
                    match t.value {
                        ScalarValue::String(s) => {
                            k = s;
                        }
                        ScalarValue::Identifier(s) => {
                            k = s;
                        }
                        e => panic!("unexpected value: {:?}", e),
                    }
                    result.insert(k, v);
                }
            }
            v => panic!("unexpected value: {:?}", v),
        }
        result
    }

    #[test]
    fn json() {
        let p = data_file_path(&["forms.conf"]);
        let f = File::open(&p).expect("Couldn't open forms.conf");
        let mut parser = Parser::new(Box::new(f)).expect("unable to create parser");
        let r = parser.mapping().expect("parse was not successful");
        let k = parser
            .consume_new_lines()
            .expect("unable to consume newlines at end");

        assert!(k == TokenKind::EOF);

        let d = make_map(r);

        assert!(d.contains_key(&"refs".to_string()));
        assert!(d.contains_key(&"fieldsets".to_string()));
        assert!(d.contains_key(&"forms".to_string()));
        assert!(d.contains_key(&"modals".to_string()));
        assert!(d.contains_key(&"pages".to_string()));
    }

    #[test]
    fn config_file() {
        let p = data_file_path(&["forms.cfg"]);
        let f = File::open(&p).expect("Couldn't open forms.cfg");
        let mut parser = Parser::new(Box::new(f)).expect("unable to create parser");
        let r = parser.mapping_body().expect("parse was not successful");
        let d = make_map(r);

        assert!(parser.at_end());
        assert!(d.contains_key(&"refs".to_string()));
        assert!(d.contains_key(&"fieldsets".to_string()));
        assert!(d.contains_key(&"forms".to_string()));
        assert!(d.contains_key(&"modals".to_string()));
        assert!(d.contains_key(&"pages".to_string()));
    }

    // Config API tests

    #[test]
    fn basic() {
        let cfg = Config::new();

        assert!(cfg.no_duplicates);
        //        assert!(cfg.strict_conversions);
        assert!(!cfg.contains_key("foo"));
        match cfg.get("bar") {
            Err(e) => match e {
                ConfigError::NotLoaded => {}
                _ => panic!("unexpected error type"),
            },
            _ => panic!("unexpected success"),
        }
    }

    #[test]
    fn duplicates() {
        let p = data_file_path(&["derived", "dupes.cfg"]);
        let mut cfg = Config::new();

        // As nothing loaded, get should give a suitable error
        match cfg.get("foo") {
            Err(e) => match e {
                ConfigError::NotLoaded => {}
                _ => panic!("expecting NotLoaded, got {:?}", e),
            },
            Ok(v) => panic!("expecting NotLoaded, got {:?}", v),
        }
        match cfg.load_from_file(&p) {
            Err(ConfigError::DuplicateKey(key, loc, orig_loc)) => {
                assert_eq!(key, "foo".to_string());
                assert_eq!(loc, loc!(4, 1));
                assert_eq!(orig_loc, loc!(1, 1));
            }
            _ => panic!("the expected error was not returned"),
        }
        cfg.no_duplicates = false;
        match cfg.load_from_file(&p) {
            Ok(()) => {
                // TODO check that the value of cfg['foo'] == 'not again!'
                assert_eq!(
                    "not again!".to_string(),
                    cfg.get("foo").unwrap().as_string()
                );
            }
            _ => panic!("unexpected failure"),
        }
    }

    #[test]
    fn context() {
        let p = data_file_path(&["derived", "context.cfg"]);

        match Config::from_file(&p) {
            Ok(mut cfg) => {
                let mut ctx = HashMap::new();

                ctx.insert(
                    "bozz".to_string(),
                    Value::Base(ScalarValue::String("bozz-bozz".to_string())),
                );
                cfg.set_context(ctx);
                assert_eq!("buzz".to_string(), cfg.get("fizz").unwrap().as_string());
                assert_eq!("bozz-bozz".to_string(), cfg.get("baz").unwrap().as_string());
                match cfg.get("bad") {
                    Ok(v) => panic!("Expected error, but got {:?}", v),
                    Err(e) => match e {
                        ConfigError::UnknownVariable(s, loc) => {
                            assert_eq!("not_there".to_string(), s);
                            assert_loc!(loc, 3, 7);
                        }
                        _ => panic!("Expected error wasn't found, got {:?}", e),
                    },
                }
            }
            _ => panic!("unexpected failure"),
        }
    }

    #[test]
    fn bad_paths() {
        let cases: Vec<(&str, RecognizerError)> = vec![
            ("foo [1, 2", RecognizerError::UnexpectedListSize(loc!(1, 6))),
            ("foo [1] bar", RecognizerError::TrailingText(loc!(1, 9))),
            (
                "foo.",
                RecognizerError::UnexpectedToken(
                    token_text(TokenKind::Word),
                    token_text(TokenKind::EOF),
                    loc!(1, 5),
                ),
            ),
            ("foo.123", RecognizerError::TrailingText(loc!(1, 4))),
            ("foo[]", RecognizerError::UnexpectedListSize(loc!(1, 5))),
            ("foo[1a]", RecognizerError::InvalidNumber(loc!(1, 6))),
            (
                "4",
                RecognizerError::UnexpectedToken(
                    token_text(TokenKind::Word),
                    token_text(TokenKind::Number),
                    loc!(1, 1),
                ),
            ),
        ];

        for case in cases {
            let r = parse_path(case.0);
            assert_eq!(case.1, r.expect_err("An error was expected, but found: "));
        }
    }

    #[test]
    fn identifiers() {
        let cases = vec![
            ("foo", true),
            ("\u{0935}\u{092e}\u{0938}", true),
            (
                "\u{73b0}\u{4ee3}\u{6c49}\u{8bed}\u{5e38}\u{7528}\u{5b57}\u{8868}",
                true,
            ),
            ("foo ", false),
            ("foo[", false),
            ("foo [", false),
            ("foo.", false),
            ("foo .", false),
            ("\u{0935}\u{092e}\u{0938}.", false),
            (
                "\u{73b0}\u{4ee3}\u{6c49}\u{8bed}\u{5e38}\u{7528}\u{5b57}\u{8868}.",
                false,
            ),
            ("9", false),
            ("9foo", false),
            ("hyphenated-key", false),
        ];

        for case in cases {
            let r = is_identifier(case.0);
            assert_eq!(case.1, r)
        }
    }

    #[test]
    fn good_paths() {
        let unary = ASTValue::Unary(UnaryNode {
            kind: TokenKind::Minus,
            operand: Box::new(ASTValue::TokenValue(Token {
                kind: TokenKind::Word,
                text: "bar".to_string(),
                value: ScalarValue::Identifier("bar".to_string()),
                start: loc!(1, 6),
                end: loc!(1, 8),
            })),
            start: loc!(1, 5),
        });

        let tokens = vec![
            Token {
                kind: TokenKind::Word,
                text: "foo".to_string(),
                value: ScalarValue::Identifier("foo".to_string()),
                start: loc!(1, 1),
                end: loc!(1, 3),
            },
            Token {
                kind: TokenKind::Word,
                text: "baz".to_string(),
                value: ScalarValue::Identifier("baz".to_string()),
                start: loc!(1, 11),
                end: loc!(1, 13),
            },
            Token {
                kind: TokenKind::Word,
                text: "bozz".to_string(),
                value: ScalarValue::Identifier("bozz".to_string()),
                start: loc!(1, 15),
                end: loc!(1, 18),
            },
            Token {
                kind: TokenKind::Word,
                text: "fizz".to_string(),
                value: ScalarValue::Identifier("fizz".to_string()),
                start: loc!(1, 23),
                end: loc!(1, 26),
            },
            Token {
                kind: TokenKind::Word,
                text: "futz".to_string(),
                value: ScalarValue::Identifier("futz".to_string()),
                start: loc!(1, 32),
                end: loc!(1, 35),
            },
        ];
        let slice = ASTValue::Slice(
            loc!(1, 28),
            Box::new(None),
            Box::new(Some(ASTValue::TokenValue(Token {
                kind: TokenKind::Number,
                text: "3".to_string(),
                value: ScalarValue::Integer(3),
                start: loc!(1, 29),
                end: loc!(1, 29),
            }))),
            Box::new(None),
        );

        let indexes = vec![
            ASTValue::TokenValue(Token {
                kind: TokenKind::Number,
                text: "3".to_string(),
                value: ScalarValue::Integer(3),
                start: loc!(1, 20),
                end: loc!(1, 20),
            }),
            ASTValue::TokenValue(Token {
                kind: TokenKind::String,
                text: "\'foo\'".to_string(),
                value: ScalarValue::String("foo".to_string()),
                start: loc!(1, 37),
                end: loc!(1, 41),
            }),
        ];

        let cases = vec![(
            "foo[-bar].baz.bozz[3].fizz[:3].futz['foo']",
            vec![
                PathElement::Attribute(&tokens[0]),
                PathElement::IndexedAccess(&unary),
                PathElement::Attribute(&tokens[1]),
                PathElement::Attribute(&tokens[2]),
                PathElement::IndexedAccess(&indexes[0]),
                PathElement::Attribute(&tokens[3]),
                PathElement::SliceAccess(&slice),
                PathElement::Attribute(&tokens[4]),
                PathElement::IndexedAccess(&indexes[1]),
            ],
        )];
        for case in cases {
            let r = parse_path(case.0);

            match r {
                Err(e) => panic!("Unexpected error {:?}", e),
                Ok(node) => {
                    let path_elements = unpack_path(&node);

                    if case.1.len() > 0 {
                        assert_eq!(case.1, path_elements, "failed for {}", case.0);
                    } else {
                        println!("{:#?}", path_elements);
                    }
                }
            }
        }
    }

    macro_rules! make_seq {
        ($($s: expr),+) => {{
            let mut result = vec![];

            $(result.push(CV!($s));)+
            Value::List(result)
        }};
    }
    macro_rules! make_map (
    {
        $($key:expr => $value:expr),* } => {{
            let mut m = HashMap::new();
            $(
                m.insert($key.to_string(), CV!($value));
            )*
            Value::Mapping(m)
        }};
    );

    macro_rules! CV {
        ($s: expr) => {
            Value::from($s)
        };
    }

    macro_rules! make_date {
        ($y: expr, $m: expr, $d: expr) => {
            CV!(NaiveDate::from_ymd($y, $m, $d))
        };
    }

    macro_rules! make_date_time {
        ($y: expr, $mo: expr, $d: expr, $h: expr, $mn: expr, $s: expr, $ns: expr, $os: expr) => {{
            let nd = NaiveDate::from_ymd($y, $mo, $d);
            let nt = NaiveTime::from_hms_nano($h, $mn, $s, $ns);
            let ndt = NaiveDateTime::new(nd, nt);
            let offset = FixedOffset::east($os);
            let dt = DateTime::<FixedOffset>::from_utc(ndt, offset);
            CV!(dt)
        }};
    }

    #[test]
    fn slices_and_indices() {
        let p = data_file_path(&["derived", "test.cfg"]);
        let cfg = Config::from_file(&p).expect("failed to load test.cfg");
        let the_list = make_seq!("a", "b", "c", "d", "e", "f", "g");

        // slices

        let slice_cases = vec![
            ("test_list[:]", the_list.clone()),
            ("test_list[::]", the_list.clone()),
            ("test_list[:20]", the_list.clone()),
            ("test_list[-20:4]", make_seq!("a", "b", "c", "d")),
            ("test_list[-20:20]", the_list.clone()),
            ("test_list[2:]", make_seq!("c", "d", "e", "f", "g")),
            ("test_list[-3:]", make_seq!("e", "f", "g")),
            ("test_list[-2:2:-1]", make_seq!("f", "e", "d")),
            (
                "test_list[::-1]",
                make_seq!("g", "f", "e", "d", "c", "b", "a"),
            ),
            ("test_list[2:-2:2]", make_seq!("c", "e")),
            ("test_list[::2]", make_seq!("a", "c", "e", "g")),
            ("test_list[::3]", make_seq!("a", "d", "g")),
            ("test_list[::2][::3]", make_seq!("a", "g")),
        ];

        for case in slice_cases {
            match cfg.get(case.0) {
                Err(e) => panic!("unexpected failure {:?}", e),
                Ok(v) => assert_eq!(case.1, v),
            }
        }

        // indices

        match the_list {
            Value::List(items) => {
                // non-negative indices

                for (i, item) in items.iter().enumerate() {
                    let s = format!("test_list[{}]", i);

                    match cfg.get(&s) {
                        Err(e) => panic!("unexpected failure {:?}", e),
                        Ok(v) => assert_eq!(item, &v),
                    }
                }

                // negative indices

                let n = items.len();

                for i in (1..n + 1).rev() {
                    let s = format!("test_list[-{}]", i);

                    match cfg.get(&s) {
                        Err(e) => panic!("unexpected failure {:?}", e),
                        Ok(v) => assert_eq!(items[n - i], v),
                    }
                }

                // invalid indices

                let len = n as i64;
                let bad_indices = vec![len, len + 1, -(len + 1), -(len + 2)];

                for i in bad_indices {
                    let s = format!("test_list[{}]", i);

                    match cfg.get(&s) {
                        Ok(v) => panic!("unexpected success {:?}", v),
                        Err(e) => match e {
                            ConfigError::IndexOutOfRange(index, pos) => {
                                assert_eq!(index, i);
                                assert_loc!(pos, 1, 11);
                            }
                            _ => panic!("unexpected error type {:?}", e),
                        },
                    }
                }
            }
            _ => panic!("unexpected variant for the_list"),
        }
    }

    macro_rules! assert_delta {
        ($a:expr, $b:expr) => {{
            assert_delta!($a, $b, 1.0e-6);
        }};
        ($a:expr, $b:expr, $eps:expr) => {{
            let av: f64 = match $a {
                Value::Base(ref sv) => match &sv {
                    ScalarValue::Float(f) => *f,
                    _ => panic!("not the correct type: {:?}", $a),
                },
                _ => panic!("not the correct type: {:?}", $a),
            };
            let bv: f64 = match $b {
                Value::Base(ref sv) => match &sv {
                    ScalarValue::Float(f) => *f,
                    _ => panic!("not the correct type: {:?}", $a),
                },
                _ => panic!("not the correct type: {:?}", $b),
            };
            let (a, b) = (&av, &bv);
            let eps = $eps;
            let diff = (*a - *b).abs();
            assert!(
                diff < eps,
                "assertion failed: `(left !== right)` \
                 (left: `{:?}`, right: `{:?}`, min diff: `{:?}`, diff: `{:?}`)",
                *a,
                *b,
                eps,
                diff
            );
        }};
    }

    #[test]
    fn main_config() {
        let mut cfg = Config::new();
        let ip = data_file_path(&["base"]);

        cfg.add_include(&ip);
        let p = data_file_path(&["derived", "main.cfg"]);
        cfg.load_from_file(&p).expect("failed to load main.cfg");

        let main_success_cases = vec![(
            "combined_list",
            make_seq!(
                "derived_foo",
                "derived_bar",
                "derived_baz",
                "test_foo",
                "test_bar",
                "test_baz",
                "base_foo",
                "base_bar",
                "base_baz"
            ),
            (
                "combined_map_1",
                make_map!(
                    "foo_key" => "base_foo",
                    "bar_key" => "base_bar",
                    "baz_key" => "base_baz",
                    "base_foo_key" => "base_foo",
                    "base_bar_key" => "base_bar",
                    "base_baz_key" => "base_baz",
                    "derived_foo_key" => "derived_foo",
                    "derived_bar_key" => "derived_bar",
                    "derived_baz_key" => "derived_baz",
                    "test_foo_key" => "test_foo",
                    "test_bar_key" => "test_bar",
                    "test_baz_key" => "test_baz"
                ),
            ),
            (
                "combined_map_2",
                make_map!(
                    "derived_foo_key" => "derived_foo",
                    "derived_bar_key" => "derived_bar",
                    "derived_baz_key" => "derived_baz"
                ),
            ),
        )];

        for case in main_success_cases {
            let r = cfg.get(case.0);
            match r {
                Err(e) => panic!("unexpected failure {:?}", e),
                Ok(v) => assert_eq!(case.1, v),
            }
        }

        let n1 = cfg.get("number_1").unwrap().as_i64();
        let n2 = cfg.get("number_2").unwrap().as_i64();
        let n3 = cfg.get("number_3").unwrap().as_i64();
        let n4 = cfg.get("number_4").unwrap().as_i64();

        assert_eq!(n1 & n2, n3);
        assert_eq!(n1 ^ n2, n4);

        let log_conf: Config;

        match cfg
            .get("logging")
            .expect("failed to get 'logging' sub-configuration")
        {
            Value::Config(cfg) => {
                for k in &["root", "loggers", "handlers", "formatters"] {
                    assert!(cfg.contains_key(k));
                }
                log_conf = cfg;
            }
            _ => panic!("unexpected return type"),
        }

        let log_success_cases = vec![
            ("handlers.file.filename", CV!("run/server.log")),
            ("handlers.debug.filename", CV!("run/server-debug.log")),
            ("root.handlers", make_seq!("file", "error", "debug")),
            ("root.handlers[:2]", make_seq!("file", "error")),
            ("root.handlers[::2]", make_seq!("file", "debug")),
        ];

        let log_failure_cases = vec![
            (
                "handlers.file/filename",
                ConfigError::InvalidPath(RecognizerError::TrailingText(loc!(1, 14))),
            ),
            (
                "\"handlers.file/filename",
                ConfigError::InvalidPath(RecognizerError::UnterminatedString(loc!(1, 23))),
            ),
            (
                "handlers.debug.levl",
                ConfigError::NotPresent(
                    "levl".to_string(),
                    Some(Location {
                        line: 1,
                        column: 16,
                    }),
                ),
            ),
        ];

        for case in log_failure_cases {
            match log_conf.get(case.0) {
                Ok(v) => panic!("expected failure not seen, got {:?}", v),
                Err(e) => assert_eq!(case.1, e),
            }
        }

        for case in log_success_cases {
            match log_conf.get(case.0) {
                Err(e) => panic!("unexpected failure {:?}", e),
                Ok(v) => assert_eq!(case.1, v),
            }
        }

        let test: Config;

        match cfg
            .get("test")
            .expect("failed to get 'test' sub-configuration")
        {
            Value::Config(cfg) => {
                test = cfg;
            }
            _ => panic!("unexpected return type"),
        }

        match cfg
            .get("base")
            .expect("failed to get 'base' sub-configuration")
        {
            Value::Config(_) => {}
            _ => panic!("unexpected return type"),
        }

        let test_success_cases = vec![
            ("float", CV!(1.0e-7f64), false),
            ("float2", CV!(0.3f64), false),
            ("float3", CV!(3.0f64), false),
            ("list[1]", CV!(2i64), false),
            ("dict.a", CV!("b"), false),
            ("date", make_date!(2019, 3, 28), false),
            (
                "date_time",
                make_date_time!(2019, 3, 28, 23, 27, 4, 314159000, 19800),
                false,
            ),
            (
                "neg_offset_time",
                make_date_time!(2019, 3, 28, 23, 27, 4, 314159000, -19800),
                false,
            ),
            (
                "alt_date_time",
                make_date_time!(2019, 3, 28, 23, 27, 4, 271828000, 0),
                false,
            ),
            (
                "no_ms_time",
                make_date_time!(2019, 3, 28, 23, 27, 4, 0, 0),
                false,
            ),
            ("computed", CV!(3.3), false),
            ("computed2", CV!(2.7), false),
            ("computed3", CV!(0.9), true),
            ("computed4", CV!(10.0), false),
        ];

        for case in test_success_cases {
            match test.get(case.0) {
                Err(e) => panic!("unexpected failure {:?}", e),
                Ok(v) => {
                    if !case.2 {
                        assert_eq!(case.1, v);
                    } else {
                        assert_delta!(case.1, v);
                    }
                }
            }
        }

        // test unboxers
        assert_eq!(test.get("dict.a").unwrap().as_string(), "b".to_string());
        assert_eq!(test.get("list[1]").unwrap().as_i64(), 2);
        assert_eq!(test.get("float3").unwrap().as_f64(), 3.0);
        assert_eq!(test.get("c1").unwrap().as_c64(), Complex64::new(4.0, 3.0));
        assert_eq!(test.get("boolean").unwrap().as_bool(), true);
        assert_eq!(
            test.get("date").unwrap().as_date(),
            NaiveDate::from_ymd(2019, 3, 28)
        );
        let nd = NaiveDate::from_ymd(2019, 3, 28);
        let nt = NaiveTime::from_hms_nano(23, 27, 4, 0);
        let ndt = NaiveDateTime::new(nd, nt);
        let offset = FixedOffset::east(0);
        let dt = DateTime::<FixedOffset>::from_utc(ndt, offset);
        assert_eq!(test.get("no_ms_time").unwrap().as_datetime(), dt);
    }

    #[test]
    fn example_config() {
        let mut cfg = Config::new();
        let ip = data_file_path(&["base"]);

        cfg.add_include(&ip);
        let p = data_file_path(&["derived", "example.cfg"]);
        cfg.load_from_file(&p).expect("failed to load example.cfg");

        assert_eq!(cfg.get("snowman_escaped"), cfg.get("snowman_unescaped"));

        let success_cases = vec![
            ("snowman_escaped", CV!("\u{2603}")),
            ("face_with_tears_of_joy", CV!("\u{01F602}")),
            ("unescaped_face_with_tears_of_joy", CV!("\u{01F602}")),
            ("special_value_2", CV!(env::var("HOME").unwrap())),
            (
                "special_value_3",
                make_date_time!(2019, 3, 28, 23, 27, 4, 314159000, 19800),
            ),
            ("special_value_4", CV!("bar")),
            // integers
            ("decimal_integer", CV!(123)),
            ("hexadecimal_integer", CV!(0x123)),
            ("octal_integer", CV!(83)),
            ("binary_integer", CV!(0b000100100011)),
            // floats
            ("common_or_garden", CV!(123.456)),
            ("leading_zero_not_needed", CV!(0.123)),
            ("trailing_zero_not_needed", CV!(123.0)),
            ("scientific_large", CV!(1.0e6)),
            ("scientific_small", CV!(1.0e-7)),
            ("expression_1", CV!(3.14159)),
            // complex
            ("expression_2", CV!(Complex64::new(3.0, 2.0))),
            ("list_value[4]", CV!(Complex64::new(1.0, 3.0))),
            //bool
            ("boolean_value", CV!(true)),
            ("opposite_boolean_value", CV!(false)),
            ("computed_boolean_2", CV!(false)),
            ("computed_boolean_1", CV!(true)),
            //sequence
            ("incl_list", make_seq!("a", "b", "c")),
            //mappings
            (
                "incl_mapping",
                make_map!(
                    "bar" => "baz",
                    "foo" => "bar"
                ),
            ),
            (
                "incl_mapping_body",
                make_map!(
                    "baz" => "bozz",
                    "fizz" => "buzz"
                ),
            ),
        ];

        for case in success_cases {
            match cfg.get(case.0) {
                Err(e) => panic!("unexpected error {:?}", e),
                Ok(v) => match v {
                    Value::Config(c) => {
                        let m = c.as_mapping(true).unwrap();
                        assert_eq!(case.1, Value::Mapping(m), "failed for {}", case.0);
                    }
                    _ => assert_eq!(case.1, v, "failed for {}", case.0),
                },
            }
        }

        let v = cfg.get("strings").unwrap();
        match &v {
            Value::List(strings) => {
                assert_eq!(CV!("Oscar Fingal O'Flahertie Wills Wilde"), strings[0]);
                assert_eq!(CV!("size: 5\""), strings[1]);
                assert_eq!(
                    CV!("Triple quoted form\ncan span\n'multiple' lines"),
                    strings[2]
                );
                assert_eq!(
                    CV!("with \"either\"\nkind of 'quote' embedded within"),
                    strings[3]
                );
            }
            _ => panic!("list expected, but got {:?}", v),
        }
    }

    #[test]
    fn expressions() {
        let p = data_file_path(&["derived", "test.cfg"]);
        let cfg = Config::from_file(&p).expect("failed to load test.cfg");

        let success_cases = vec![
            (
                "dicts_added",
                make_map!(
                    "a" => "b",
                    "c" => "d"
                ),
            ),
            (
                "nested_dicts_added",
                make_map!(
                    "a" => make_map!("b" => "c", "w" => "x"),
                    "d" => make_map!("e" => "f", "y" => "z")
                ),
            ),
            ("lists_added", make_seq!("a", 1, "b", 2)),
            ("list[:2]", make_seq!(1, 2)),
            ("dicts_subtracted", make_map!("a" => "b")),
            ("nested_dicts_subtracted", Value::Mapping(HashMap::new())),
            (
                "dict_with_nested_stuff",
                make_map!(
                    "a_list" => make_seq!(1, 2, make_map!("a" => 3)),
                    "a_map" => make_map!("k1" => make_seq!("b", "c", make_map!("d" => "e")))
                ),
            ),
            ("dict_with_nested_stuff.a_list[:2]", make_seq!(1, 2)),
            ("unary", CV!(-4)),
            ("abcdefghijkl", CV!("mno")),
            ("power", CV!(8)),
            ("computed5", CV!(2.5)),
            ("computed6", CV!(2)),
            ("c3", CV!(Complex64::new(3.0, 1.0))),
            ("c4", CV!(Complex64::new(5.0, 5.0))),
            ("computed8", CV!(2)),
            ("computed9", CV!(160)),
            ("computed10", CV!(62)),
            (
                "interp",
                CV!("A-4 a test_foo true 10 0.0000001 1 b [a, c, e, g]Z"),
            ),
            ("interp2", CV!("{a: b}")),
        ];

        for case in success_cases {
            match cfg.get(case.0) {
                Err(e) => panic!("unexpected failure {:?}", e),
                Ok(v) => assert_eq!(case.1, v),
            }
        }

        let failure_cases = vec![
            ("bad_include", ConfigError::StringExpected(loc!(71, 16))),
            (
                "computed7",
                ConfigError::NotPresent(
                    "float4".to_string(),
                    Some(Location {
                        line: 72,
                        column: 16,
                    }),
                ),
            ),
            (
                "bad_interp",
                ConfigError::ConversionError("${computed7}".to_string()),
            ),
        ];

        for case in failure_cases {
            match cfg.get(case.0) {
                Ok(v) => panic!("unexpected success {:?}", v),
                Err(e) => assert_eq!(case.1, e),
            }
        }
    }

    #[test]
    fn circular_references() {
        let p = data_file_path(&["derived", "test.cfg"]);
        let cfg = Config::from_file(&p).expect("failed to load test.cfg");

        let cases = vec![
            (
                "circ_list[1]",
                ConfigError::CircularReferenceError(vec![(
                    "circ_list[1]".to_string(),
                    loc!(46, 5),
                )]),
            ),
            (
                "circ_map.a",
                ConfigError::CircularReferenceError(vec![
                    (
                        "circ_map.a".to_string(),
                        Location {
                            line: 53,
                            column: 8,
                        },
                    ),
                    ("circ_map.b".to_string(), loc!(51, 8)),
                    ("circ_map.c".to_string(), loc!(52, 8)),
                ]),
            ),
        ];

        for case in cases {
            match cfg.get(case.0) {
                Ok(v) => panic!("unexpected success {:?}", v),
                Err(e) => assert_eq!(case.1, e),
            }
        }
    }

    #[test]
    fn sources() {
        let cases = vec![
            "foo[::2]",
            "foo[:]",
            "foo[:2]",
            "foo[2:]",
            "foo[::1]",
            "foo[::-1]",
            "foo[2]",
        ];

        for case in cases {
            let node = parse_path(case).unwrap();
            let s = to_source(&node);

            assert_eq!(case, s);
        }
    }

    #[test]
    fn path_across_includes() {
        let p = data_file_path(&["base", "main.cfg"]);
        let cfg = Config::from_file(&p).expect("failed to load base main.cfg");

        let cases = vec![
            ("logging.appenders.file.filename", CV!("run/server.log")),
            ("logging.appenders.file.append", CV!(true)),
            (
                "logging.appenders.error.filename",
                CV!("run/server-errors.log"),
            ),
            ("logging.appenders.error.append", CV!(false)),
            ("redirects.freeotp.url", CV!("https://freeotp.github.io/")),
            ("redirects.freeotp.permanent", CV!(false)),
        ];

        for case in cases {
            let msg = format!("failed for {}", case.0);
            assert_eq!(case.1, cfg.get(case.0).unwrap(), "{}", msg);
        }
    }

    #[test]
    fn forms() {
        let mut cfg = Config::new();
        let ip = data_file_path(&["base"]);

        cfg.add_include(&ip);
        let p = data_file_path(&["derived", "forms.cfg"]);
        cfg.load_from_file(&p).expect("failed to load forms.cfg");

        let cases = vec![
            ("modals.deletion.contents[0].id", CV!("frm-deletion")),
            (
                "refs.delivery_address_field",
                make_map!(
                    "kind" => "field",
                    "type" => "textarea",
                    "name" => "postal_address",
                    "label" => "Postal address",
                    "label_i18n" => "postal-address",
                    "short_name" => "address",
                    "placeholder" => "We need this for delivering to you",
                    "ph_i18n" => "your-postal-address",
                    "message" => " ",
                    "required" => true,
                    "attrs" => make_map!("minlength" => 10),
                    "grpclass" => "col-md-6"
                ),
            ),
            (
                "refs.delivery_instructions_field",
                make_map!(
                    "kind" => "field",
                    "type" => "textarea",
                    "name" => "delivery_instructions",
                    "label" => "Delivery Instructions",
                    "short_name" => "notes",
                    "placeholder" => "Any special delivery instructions?",
                    "message" => " ",
                    "label_i18n" => "delivery-instructions",
                    "ph_i18n" => "any-special-delivery-instructions",
                    "grpclass" => "col-md-6"
                ),
            ),
            (
                "refs.verify_field",
                make_map!(
                    "kind" => "field",
                    "type" => "input",
                    "name" => "verification_code",
                    "label" => "Verification code",
                    "label_i18n" => "verification-code",
                    "short_name" => "verification code",
                    "placeholder" => "Your verification code (NOT a backup code)",
                    "ph_i18n" => "verification-not-backup-code",
                    "attrs" => make_map!(
                            "minlength" => 6,
                            "maxlength" => 6,
                            "autofocus" => true),
                    "append" => make_map!(
                            "label" => "Verify",
                            "type" => "submit",
                            "classes" => "btn-primary"),
                    "message" => " ",
                    "required" => true
                ),
            ),
            (
                "refs.signup_password_field",
                make_map!(
                    "kind" => "field",
                    "type" => "password",
                    "label" => "Password",
                    "label_i18n" => "password",
                    "message" => " ",
                    "name" => "password",
                    "ph_i18n" => "password-wanted-on-site",
                    "placeholder" => "The password you want to use on this site",
                    "required" => true,
                    "toggle" => true
                ),
            ),
            (
                "refs.signup_password_conf_field",
                make_map!(
                    "kind" => "field",
                    "type" => "password",
                    "name" => "password_conf",
                    "label" => "Password confirmation",
                    "label_i18n" => "password-confirmation",
                    "placeholder" => "The same password, again, to guard against mistyping",
                    "ph_i18n" => "same-password-again",
                    "message" => " ",
                    "toggle" => true,
                    "required" => true
                ),
            ),
            (
                "fieldsets.signup_ident[0].contents[0]",
                make_map!(
                    "kind" => "field",
                    "type" => "input",
                    "name" => "display_name",
                    "label" => "Your name",
                    "label_i18n" => "your-name",
                    "placeholder" => "Your full name",
                    "ph_i18n" => "your-full-name",
                    "message" => " ",
                    "data_source" => "user.display_name",
                    "required" => true,
                    "attrs" => make_map!("autofocus" => true),
                    "grpclass" => "col-md-6"
                ),
            ),
            (
                "fieldsets.signup_ident[0].contents[1]",
                make_map!(
                    "kind" => "field",
                    "type" => "input",
                    "name" => "familiar_name",
                    "label" => "Familiar name",
                    "label_i18n" => "familiar-name",
                    "placeholder" => "If not just the first word in your full name",
                    "ph_i18n" => "if-not-first-word",
                    "data_source" => "user.familiar_name",
                    "message" => " ",
                    "grpclass" => "col-md-6"
                ),
            ),
            (
                "fieldsets.signup_ident[1].contents[0]",
                make_map!(
                    "kind" => "field",
                    "type" => "email",
                    "name" => "email",
                    "label" => "Email address (used to sign in)",
                    "label_i18n" => "email-address",
                    "short_name" => "email address",
                    "placeholder" => "Your email address",
                    "ph_i18n" => "your-email-address",
                    "message" => " ",
                    "required" => true,
                    "data_source" => "user.email",
                    "grpclass" => "col-md-6"
                ),
            ),
            (
                "fieldsets.signup_ident[1].contents[1]",
                make_map!(
                    "kind" => "field",
                    "type" => "input",
                    "name" => "mobile_phone",
                    "label" => "Phone number",
                    "label_i18n" => "phone-number",
                    "short_name" => "phone number",
                    "placeholder" => "Your phone number",
                    "ph_i18n" => "your-phone-number",
                    "classes" => "numeric",
                    "message" => " ",
                    "prepend" => make_map!("icon" => "phone"),
                    "attrs" => make_map!("maxlength" => 10),
                    "required" => true,
                    "data_source" => "customer.mobile_phone",
                    "grpclass" => "col-md-6"
                ),
            ),
        ];

        for case in cases {
            match cfg.get(case.0) {
                Err(e) => panic!("unexpected failure {:?}", e),
                Ok(v) => assert_eq!(case.1, v),
            }
        }
    }

    #[test]
    fn absolute_include_path() {
        let mut p = data_file_path(&["derived", "test.cfg"]);
        p = canonicalize(&p)
            .unwrap()
            .to_str()
            .unwrap()
            .replace("\\", "/") // for Windows - avoid escape sequence-like stuff
            .to_string();

        let source = "test: @'foo'".replace("foo", &p);
        let mut cfg = Config::new();

        cfg.load(Box::new(Cursor::new(source)))
            .expect("couldn't load from source");
        match cfg.get("test.computed6") {
            Err(e) => panic!("unexpected failure {:?}", e),
            Ok(v) => assert_eq!(2i64, v.as_i64()),
        }
    }

    #[test]
    fn nested_include_path() {
        let p = data_file_path(&["base", "top.cfg"]);
        let mut ip = data_file_path(&["derived"]);
        let mut cfg = Config::new();

        cfg.add_include(&ip);
        ip = data_file_path(&["another"]);
        cfg.add_include(&ip);
        cfg.load_from_file(&p).expect("failed to load forms.cfg");

        match cfg.get("level1.level2.final") {
            Err(e) => panic!("unexpected failure {:?}", e),
            Ok(v) => assert_eq!(42i64, v.as_i64()),
        }
    }

    #[test]
    fn windows_line_endings() {
        let p = data_file_path(&["derived", "testwin.cfg"]);
        let cfg = Config::from_file(&p).expect("failed to load testwin.cfg");
    }

    #[test]
    fn wip_locations() {
        /*
                let p = data_file_path(&["derived", "test.cfg"]);
                let mut f = File::open(&p).expect("Couldn't open test.cfg");
                let mut tokenizer = Tokenizer::new(Box::new(f));
                let mut t = tokenizer.get_token().expect("a token was expected");

                while t.kind != TokenKind::EOF {
                    let kind = format!("{:?}", t.kind);
                    println!(
                        "({:>3} {:>3}) - ({:>3} {:>3}) {:>12} {}",
                        t.start.line, t.start.column, t.end.line, t.end.column, kind, t.text
                    );
                    t = tokenizer.get_token().expect("a token was expected");
                }
                println!("Done.");
        */
    }
}
