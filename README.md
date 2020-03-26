The CFG configuration format is a text format for configuration files which is similar to, and a superset of, the JSON format. It dates from [2008](https://wiki.python.org/moin/HierConfig) and has the following aims:

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

You can load and query the above configuration using, for example, [the evcxr REPL](https://github.com/google/evcxr/blob/master/evcxr_repl/README.md):

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

The successful [`from_file()`](config/struct.Config.html#method.from_file) call returns a [`Config`](config/struct.Config.html) instance which can be used to query the configuration.

Access elements with keys
-------------------------
Accessing elements of the configuration with a simple key is not much harder than using a `HashMap`:
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
Here, the desired value is obtained in a single step, by (under the hood) walking the path `c.d` – first getting the mapping at key `c`, and then the value at `d` in the resulting mapping.

Note that you can have simple keys which look like paths:
```text
>> cfg.get("f.g")
Ok(Base(String("h")))
```
If a key is given that exists in the configuration, it is used as such, and if it is not present in the configuration, an attempt is made to interpret it as a path. Thus, `f.g` is present and accessed via key, whereas `c.d` is not an existing key, so is interpreted as a path.

Access to date/time objects
---------------------------
You can also get native Rust date/time objects from a configuration, by using an ISO date/time pattern in a backtick-string:
```text
>> cfg.get("christmas_morning")
Ok(Base(DateTime(2019-12-25T08:39:49+00:00)))
```
You get either NaiveDate objects, if you specify the date part only, or else DateTime<FixedOffset> objects, if you specify a time component as well. If no offset is specified, it is assumed to be zero.

Access to environment variables
-------------------------------
To access an environment variable, use a backtick-string of the form `$VARNAME`:
```text
>> cfg.get("home")
Ok(Base(String("/home/vinay")))
```
You can specify a default value to be used if an environment variable isn’t present using the `$VARNAME|default-value` form. Whatever string follows the pipe character (including the empty string) is returned if the VARNAME is not a variable in the environment.
```text
>> cfg.get("foo")
Ok(Base(String("bar")))
```

For more information, see [the CFG documentation](https://docs.red-dove.com/cfg/index.html).
