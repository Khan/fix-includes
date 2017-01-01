# fix-includes

Fix-includes manages include/import/require lines in C, C++, Python,
and JavaScript (node.js).  It is easy to add support for other
languages as well.


## What does fix-includes do?

Fix-includes is a tool to manage "include" lines in medium and large
software projects.  It easily scales to tens of thousands of source
files.

An "include line" is a directive, present in most languages, that
allows you to use another source file from the source file that
contains the include line.  The syntax differs between languages:
```
    #include <stdio.h>       // C
    import sys               // Python
    var fs = require("fs");  // JavaScript (node.js)
    ...
```
In this project, all such lines are called "include lines," regardless
of the syntax (and regardless of whether they include or import).

### Sorting and reordering

Many projects have style rules concerning their include lines.  For
instance, the [Google C++ style
guide](https://google.github.io/styleguide/cppguide.html#Names_and_Order_of_Includes)
requires the includes to be divided into three sections: one for
system includes, one for third-party includes, and one (sometimes two)
for project includes, with a blank line between each section.  It
further requires that the includes be sorted alphabetically within
each section.

This project will automatically detect include lines within a file and
reorder them so they follow such a rule.

### Adding and deleting

When refactoring, you sometimes want to split a file in two, and as a
result all files that include foo.h (say) will now also need to
include bar.h.  Fix-includes makes it easy to do this, without any
need for IDE support.

Or perhaps you have combined two files into one, and bar.h is no
longer needed anywhere.  Fix-includes can easily delete it from all
source files.


## Why is this hard?

Some readers might be thinking at this point, "Why is there a whole
project for this?  My IDE does it for me!"  Or maybe they're thinking,
"I can do it in one line of Perl!"  It turns out includes are more
complex than they seem at first, and these simplistic solutions often
fall short.

1. **Comments**.  When you move an include around, you want to move
   its comments around as well!
   ```
       // This gimlitzes the frobnitzes
       #include "gimlitz_frotnitzes.h"
       // Once you've gimlitzed the frobnitzes, you'll want to
       // frobozz them!  Can you imagine not frobozzing them?
       #include "frobozz_frobnitzes.h"
   ```

1. **Multi-line includes.**  If you just highlight your include-lines
   and press "sort" in your favorite IDE, it will have trouble with
   multi-line includes:
   ```
       import foo
       from bar import (
            bar1, bar2, bar3)
       from baz import bazalicious
   ```

1. **Interleaved includes and code.**  Sometimes reordering includes
   can cause errors:
   ```
   var i18n = require("./i8n.js);
   var gettext = i18n.gettext;
   var underline = require("./underline.js");
   ```

1. **Inline includes.**  It would be nice to obey the style rules
   for includes that are not at the top of the file:
   ```
   def dump_upon_write_error():
       import sys
       import os
       import traceback
       # write() may be broken here!  Use os.write() instead.     
       os.write(sys.stdout.fileno(), traceback.format_stack())
   ```

1. **Avoiding duplicates.**  When adding a new include, you want to
   make sure you don't add it if it's already there.  It's especially
   easy to get this wrong when the original and the new addition have
   whitespace differences:
   ```
      var foo = require("./foo.js");
      var x   = require(
           "./path/to/some/third_party/library/containing/x.js");
      // And now you request to add:
      //    var x = require("./path/to/some/third_party/library/containing/x.js");
   ```

Don't worry about any of these things, or the other myriad things that
can go wrong when trying to fix includes automatically (such as
associating a top-of-file docstring with an include line!)  Just use
this script!


## How do I use it?

You just run
```
   fix_includes.py <file> ...
```

It will detect the type of the file from its extension, or you can
specify it manually.  By default, fix-includes will sort and
reorganize includes, using a built-in rule that matches the [Google
C++ style
guide](https://google.github.io/styleguide/cppguide.html#Names_and_Order_of_Includes).
The rules should be fairly easy to configure, though it requires
knowledge of Python to do so.

You can also run
```
   fix_includes.py --delete "substring" <file> ...
```
to delete all include-lines that match `substring` (comments are omitted
before doing the substring match) in the specified files.  This will
sort and organize the include lines as well.  Or you can run
```
   fix_includes.py --add "line" <file> ...
```
to add `line` as an include-line to all specified files.  Again, this
also sorts.  You can combine `--add` and `--delete` as well.

*Transitional*: Until I am done integrating js and python into 
fix_includes.py, there are separate files for them: fix_js_requires.py
and fix_python_imports.py.

## What are the default sort rules?

TODO

## Other projects

**Python:** If all you are interested in is sorting, and your code is
Python-only, you may be interested in
[isort](https://github.com/timothycrosley/isort), which provides
features not found in fix-includes.
