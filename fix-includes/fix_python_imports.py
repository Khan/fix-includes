#!/usr/bin/env python

##===--- fix_includes.py - rewrite source files based on iwyu output ----===##
#
#                     The LLVM Compiler Infrastructure
#
# This file is distributed under the University of Illinois Open Source
# License:
#
# ============================================================================
# LLVM Release License
# ============================================================================
# University of Illinois/NCSA
# Open Source License
#
# Copyright (c) 2003-2010 University of Illinois at Urbana-Champaign.
# All rights reserved.
#
# Developed by:
#
# LLVM Team
#
# University of Illinois at Urbana-Champaign
#
# http://llvm.org
#
# Permission is hereby granted, free of charge, to any person
# obtaining a copy of this software and associated documentation files
# (the "Software"), to deal with the Software without restriction,
# including without limitation the rights to use, copy, modify, merge,
# publish, distribute, sublicense, and/or sell copies of the Software,
# and to permit persons to whom the Software is furnished to do so,
# subject to the following conditions:
#
# * Redistributions of source code must retain the above copyright
# notice, this list of conditions and the following disclaimers.
#
# * Redistributions in binary form must reproduce the above copyright
# notice, this list of conditions and the following disclaimers in the
# documentation and/or other materials provided with the distribution.
#
# * Neither the names of the LLVM Team, University of Illinois at
# Urbana-Champaign, nor the names of its contributors may be used to
# endorse or promote products derived from this Software without
# specific prior written permission.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE CONTRIBUTORS OR COPYRIGHT
# HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
# IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
# IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS WITH
# THE SOFTWARE.
##===--------------------------------------------------------------------===##

"""Update files with the 'correct' import lines.

Given a description (described below) of how the 'import' lines of a
given list of python source file should change, modify the files so their
'import' lines match the description.  Possible changes include
deleting 'import' lines and adding new 'import' lines.  This
script will also sort and order the 'import' lines (so third-party
imports come in their own section, for instance).

This script runs in four stages.  In the first, it groups physical
lines together to form 'move spans'.  A 'move span' is the atomic unit
for moving or deleting code.  A move span is either a) an import line,
along with any comment lines immediately preceding it; or b) any other
single line.  Example:

   // Boy this import line is really long!
   from my_very_important_module import (
       long_function_name_a, long_function_name_b)

Then, it groups move spans together into 'reorder spans'.  These are
spans of code that consist entirely of import lines, maybe separated
by blank lines and comments.  We assume that we can arbitrarily
reorder import lines within a reorder span, without affecting
correctness.  Things like other var definitions, function definisions,
etc -- just about anything -- break up reorder spans.

In stage 3 it deletes all import lines that the input says to delete.

In stage 4 it adds new import lines after the last existing import
lines.  Then it reorders the import lines to match a canonical,
hard-coded order.  Note that for correctness, reordering never allows
a import line to leave its reorder span.

All this moving messes up the blank lines, which we then need to fix
up.  Then we're done!

The input description consists of sections that look like so:

   <filename> should add these lines:
   <line of text to be inserted, verbatim>
   ...
   <blank line>

and

   <filename> should remove these lines:
   <substring matching line of text to be removed> OR <line number to remove>
   ...
   <blank line>

The first line of text that includes the matching substring will be
removed, along with the rest of its move span (so leading comments,
blank lines, etc.)  Instead of listed a substring you can list a
number, which is taken to be the line number to delete.  (If you
want to delete all lines matching a substring like "15", you're
out of luck.)  Line numbers start at 1 for the first line.

It is fine to specify the same filename in multiple sections; they
will get merged together.
"""


import difflib
import optparse
import os
import pipes  # For (undocumented) pipes.quote
import pkgutil
import re
import sys
import subprocess


_USAGE = """\
%prog [options] [filename] ... < <change description>
    OR %prog -s [other options] <filename> ...

%prog reads a change description on stdin and, unless --sort_only or
--dry_run is specified, modifies the files mentioned in the change
description, removing their old 'import' lines and replacing them
with the lines given by the input.  It also sorts the import lines.

All files mentioned in the input are modified, unless filenames are
specified on the commandline, in which case only those files are
modified.

The exit code is the number of files that were modified (or that would
be modified if --dry_run was specified) unless that number exceeds 127,
in which case 127 is returned.

The input description consists of sections that look like so:

   <filename> should add these lines:
   <line of text to be inserted, verbatim>
   ...
   <blank line>

and

   <filename> should remove these lines:
   <substring matching line of text to be removed> OR <line number to remove>
   ...
   <blank line>
"""

_COMMENT_RE = re.compile(r'\s*#.*')

# These are the types of lines a file can have.  These should all
# start with ^, so they match at the beginning of a line.  You should
# avoid the case where two regexp's can make the same line.

_DOCSTRING_COMMENT_RE = re.compile(r'^""".*?"""', re.DOTALL | re.M)
_COMMENT_LINE_RE = re.compile(r'^\s*#.*', re.M)
# This is surprisingly complicated due to how ^ and $ work with re.M
_BLANK_LINE_RE = re.compile(r'^[^\S\r\n]*(\r\n|\r|\n)|^\s+$', re.M)
# The group (in parens) holds the unique 'key' identifying this
# import.  This is annoying because of line continuations, which can
# either have a \ at the end of the line or parens.  (Luckily, nested
# parens are unlikely.)
_IMPORT_RE = re.compile(r'^(?:import|from)\s*([^\\(\n]*(?:\\\n.*|\([^)]*\))*)',
                        re.M)
# This 'fake' re is used when an import spans multiple lines:
#   from my_very_important_module import (
#       long_function_name_a, long_function_name_b)
_IMPORT_CONTINUATION_RE = re.compile(r'$.^')     # a never-matching RE

# We annotate every line in the source file by the re it matches, or None.
_LINE_TYPES = [_DOCSTRING_COMMENT_RE, _COMMENT_LINE_RE,
               _BLANK_LINE_RE, _IMPORT_RE, _IMPORT_CONTINUATION_RE,
              ]


class FixIncludesError(Exception):
  pass


class ChangeRecord(object):
  """Information from stdin indicating one file to change."""

  def __init__(self, filename):
    self.filename = filename

    self.imports_to_add = set()
    # Each element of this set is either a string or an int.
    # If a string, we delete all lines matching that string.
    # If an int, we delete that line-number.
    self.substrings_or_indexes_of_lines_to_delete = set()

  def Merge(self, other):
    """Merges other with this one.  They must share a filename.

    This function is intended to be used when we see two records
    in the input, both for the same file.  We can merge the two together.
    We are conservative: we union the lines to add, and intersect the
    lines to delete.

    Arguments:
      other: a ChangeRecord to merge into this one.
        It must have the same value for filename that self does.
    """
    assert self.filename == other.filename, "Can't merge distinct files"
    self.imports_to_add.update(other.imports_to_add)
    self.substrings_or_indexes_of_lines_to_delete.intersection_update(
      other.substrings_or_indexes_of_lines_to_delete)

  def HasContentfulChanges(self):
    """Returns true iff this record has at least one add or delete."""
    return bool(self.imports_to_add or
                self.substrings_or_indexes_of_lines_to_delete)

  def __str__(self):
    return ('--- input record ---\n  FILENAME: %s\n'
            '  LINES TO DELETE: %s\n   TO ADD: %s\n---\n'
            % (self.filename, self.substrings_or_indexes_of_lines_to_delete,
               self.imports_to_add))


class ChangeRecordParser(object):
  """Parses the lines in the input corresponding to one source file."""

  # The input to this script is formatted as follows: a 'header' line
  # indicating the file affected (one of the two lines below), followed
  # by a list of line-contents to either add or remove.  (In the case
  # of removing, it can be just a substring of the line contents.)
  # The record is terminated by a blank line.
  _ADD_RE = re.compile(r'^(.*) should add these lines:$')
  _REMOVE_RE = re.compile(r'^(.*) should remove these lines:$')

  def ParseOneRecord(self, infile):
    """Given a file object with the input to our script, return per file info.

    For each source file the input mentions, we return a ChangeRecord.
    input must be iterable, and return a line per iteration (any file
    object will do).

    Returns:
       An ChangeRecord object, or None at EOF.

    Raises:
       FixIncludesError: for malformed-looking lines in the input.
    """
    retval = None
    record_type = None

    for line in infile:
      line = line.strip()
      if not line:            # blank line ends our record
        if retval:
          return retval
        continue

      if record_type == self._ADD_RE:
        retval.imports_to_add.add(line)
        continue

      if record_type == self._REMOVE_RE:
        if line.isdigit():     # the user entered a line-number
          retval.substrings_or_indexes_of_lines_to_delete.add(int(line))
        else:                  # the user entered a substring
          retval.substrings_or_indexes_of_lines_to_delete.add(line)
        continue

      m = self._ADD_RE.match(line)
      if m:
        retval = ChangeRecord(m.group(1))
        record_type = self._ADD_RE
        continue

      m = self._REMOVE_RE.match(line)
      if m:
        retval = ChangeRecord(m.group(1))
        record_type = self._REMOVE_RE
        continue

      raise FixIncludesError('Unexpected header line %s in input' % line)


class LineInfo(object):
  """Information about a single line of a source file."""

  def __init__(self, line):
    """Initializes the content of the line, but no ancillary fields."""
    # The content of the line in the input file
    self.line = line

    # The 'type' of the line.  The 'type' is one of the regular
    # expression objects in _LINE_TYPES, or None for any line that
    # does not match any regular expression in _LINE_TYPES.
    self.type = None

    # True if no lines processed before this one have the same type
    # as this line.
    self.is_first_line_of_this_type = False

    # Set to true if we want to delete/ignore this line in the output
    # (for instance, because the input says to delete this line).  At the
    # start, the only line to delete is the 'dummy' line 0.
    self.deleted = self.line is None

    # If this line is a import line, gives a [begin,end) pair saying
    # the 'span' this line is part of.  We do this for two types of
    # span: the move span (a import line, along with any preceding
    # comments) and the reorder span (a continguous block of
    # move-spans, connected only by blank lines and comments).  For
    # lines that are not a import line, these may have an arbitrary
    # value.
    self.move_span = None
    self.reorder_span = None

    # If this line is a import-line, gives the 'key' of the line: the
    # name of the file being imported.  For other types of lines,
    # this is None.
    self.key = None

  def __str__(self):
    if self.deleted:
      line = 'XX-%s-XX' % self.line
    else:
      line = '>>>%s<<<' % self.line
    if self.type is None:
      type_id = None
    else:
      type_id = _LINE_TYPES.index(self.type)
    return ('%s\n  -- type: %s (key: %s).  move_span: %s.  reorder_span: %s'
            % (line, type_id, self.key, self.move_span, self.reorder_span))


def _ReadFile(filename):
  """Read from filename and return a list of file lines."""
  try:
    return open(filename).read()
  except (IOError, OSError), why:
    print "Skipping '%s': %s" % (filename, why)
  return None


def _WriteFileContentsToFileObject(f, file_lines, line_ending):
  """Write the given file-lines to the file."""
  f.write(line_ending.join(file_lines))
  f.write(line_ending)


def _DetectLineEndings(filename):
  """Detect line ending of given file."""

  # Find out which file ending is used first. The
  # first lines indicate the line ending for the whole file
  # so pathological files with mixed endings aren't handled properly!
  f = open(filename, 'U')
  try:
    while f.newlines is None:
      if f.readline() == '':
        break
    return f.newlines if f.newlines != None and \
        type(f.newlines) is not tuple else '\n'
  finally:
    f.close()


def _WriteFileContents(filename, file_lines):
  """Write the given file-lines to the file."""
  try:
    line_ending = _DetectLineEndings(filename)
    # Open file in binary mode to preserve line endings
    f = open(filename, 'wb')
    try:
      _WriteFileContentsToFileObject(f, file_lines, line_ending)
    finally:
      f.close()
  except (IOError, OSError), why:
    print "Error writing '%s': %s" % (filename, why)


def _CreateCommandLine(command, args):
  """Join the command with the args in a shell-quoted way."""
  ret = '%s %s' % (command, ' '.join(map(pipes.quote, args)))
  print 'Running:', ret
  return ret


def _GetCommandOutputLines(command, args):
  """Return an iterable over the output lines of the given shell command."""
  full_command = _CreateCommandLine(command, args)
  proc = subprocess.Popen(full_command, shell=True, stdout=subprocess.PIPE)
  return proc.stdout


def _RunCommand(command, args):
  """Run the given shell command."""
  for line in _GetCommandOutputLines(command, args):
    print line,


def _GetCommandOutputWithInput(command, stdin_text):
  """Return the output of the given command fed the stdin_text."""
  print command
  proc = subprocess.Popen(command,
                          stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE,
                          shell=True)
  return proc.communicate(input=stdin_text)[0]


def PrintFileDiff(old_file_contents, new_file_contents):
  """Print a unified diff between files, specified as lists of lines."""
  diff = difflib.unified_diff(old_file_contents, new_file_contents)
  # skip the '--- <filename>/+++ <filename>' lines at the start
  try:
    diff.next()
    diff.next()
    print '\n'.join(diff)
  except StopIteration:
    pass


def _CalculateLineTypesAndKeys(file_contents, change_record):
  """Fills file_line's type and key fields, where the type is a regexp object.

  We match each line (line_info.line) against every regexp in
  _LINE_TYPES, and assign the first that matches, or None if none
  does.

  Sets file_line.type and file_line.is_first_line_of_this_type for
  each file_line in file_lines.

  Arguments:
    file_contents: an array of LineInfo objects with .line fields filled in.
    change_record: the ChangeRecord struct for this source file.

  Returns:
    An array of LineInfo objects with .line and .type fields filled in.
    The first LineInfo is a sentinel, with .line = None and .type = None.
  """
  file_lines = [LineInfo(None)]
  if not file_contents:
    return file_lines

  for line in file_contents.splitlines():
    file_lines.append(LineInfo(line))

  # Figure out span of each line.  We have to split again because this
  # time we need to preserve the newlines.
  pos_to_linenum = {}     # char-position at beginning of line -> line number
  linenum_to_pos = [-1]   # line number -> char-position of beginning of line
  pos = 0
  for (i, line) in enumerate(file_contents.splitlines(True)):
    pos_to_linenum[pos] = i + 1
    linenum_to_pos.append(pos)
    pos += len(line)
  linenum_to_pos.append(pos)     # sentinel

  # Figure out the next occurrence of each thing we're looking for.
  pos = 0
  next_matches = {}
  for regex in _LINE_TYPES:
    m = regex.search(file_contents)
    if m:
      next_matches[regex] = (m.start(), m.end(), m.groups())
    else:
      next_matches[regex] = None

  # Now keep looping until we can't find anything anymore.
  seen_types = set()
  while any(next_matches.itervalues()):
    sorted_matches = sorted(next_matches.iteritems(),
                            key=lambda (_, m): m if m else (sys.maxint, 0, ''))
    (regex, (match_start, match_end, match_groups)) = sorted_matches[0]

    # We require each regex to match at beginning of line, so
    # this lookup should succeed.
    next_linenum = pos_to_linenum[match_start]

    # Every line that our regexp spans has our type.  Exception is for
    # type _IMPORT_RE, where subsequent lines get type
    # _IMPORT_CONTINUATION_LINE.  _IMPORT_RE (only) also gets a key.
    key = None
    while linenum_to_pos[next_linenum] < match_end:
      if regex == _IMPORT_RE:
        key = match_groups[0].strip()

      file_lines[next_linenum].key = key
      file_lines[next_linenum].type = regex
      file_lines[next_linenum].is_first_line_of_this_type = (
        file_lines[next_linenum].type not in seen_types)
      seen_types.add(file_lines[next_linenum].type)

      if regex == _IMPORT_RE:
        regex = _IMPORT_CONTINUATION_RE   # for subsequent lines
      next_linenum += 1

    pos = linenum_to_pos[next_linenum]

    # Update next_matches for everyone.  We re-do anyone whose start
    # was inside our range (e.g. a blank line inside a comment).
    for (regex, match_info) in next_matches.items():
      match_start = match_info[0] if match_info else sys.maxint
      if match_start < pos:
          m = regex.search(file_contents[pos:])
          if m and m.start() + pos < len(file_contents):
            next_matches[regex] = (m.start() + pos, m.end() + pos, m.groups())
          else:
            next_matches[regex] = None

  return file_lines


def _PreviousNondeletedLine(file_lines, line_number):
  """Returns the line number of the previous not-deleted line, or None."""
  for line_number in xrange(line_number - 1, -1, -1):
    if not file_lines[line_number].deleted:
      return line_number
  return None


def _NextNondeletedLine(file_lines, line_number):
  """Returns the line number of the next not-deleted line, or None."""
  for line_number in xrange(line_number + 1, len(file_lines)):
    if not file_lines[line_number].deleted:
      return line_number
  return None


def _LineNumberStartingPrecedingComments(file_lines, line_number):
  """Returns the line-number for the comment-lines preceding the given linenum.

  Looking at file_lines, look at the lines immediately preceding the
  given line-number.  If they're comment lines, return the first line
  of the comment lines preceding the given line.  Otherwise, return
  the given line number.

  As a special case, if the comments go all the way up to the first
  line of the file (line 1), we assume they're header-comment lines,
  which are special -- they're not associated with any source code
  line -- and we return line_number in that case.

  Likewise, we do not consider top-of-file docstrings to be associated
  with the import line.

  Arguments:
    file_lines: an array of LineInfo objects, with .type fields filled in.
    line_number: an index into file_lines.

  Returns:
    The first line number of the preceding comments, or line_number
      if there are no preceding comments or they appear to be a
      top-of-file header-comment or a javadoc-style comment.

  """
  retval = line_number
  while retval > 0 and file_lines[retval - 1].type == _COMMENT_LINE_RE:
    retval -= 1
  if retval <= 1:          # top-of-line comments
    retval = line_number   # so ignore all the comment lines
  return retval


def _CalculateMoveSpans(file_lines):
  """Fills each input_line's move_span field.

  A 'move span' is a range of lines (from file_lines) that includes a
  import and all the comments preceding it.  It is the unit we would
  move if we decided to move (or delete) this import.

  For lines of type _IMPORT_RE, the move span is set to the tuple
  [start_of_span, end_of_span).  All other lines have the move span
  kept at None.

  Arguments:
    file_lines: an array of LineInfo objects, with .type fields filled in.
  """
  for line_number in xrange(len(file_lines)):
    if file_lines[line_number].type == _IMPORT_RE:
      span_begin = _LineNumberStartingPrecedingComments(file_lines,
                                                        line_number)
      span_end = line_number + 1
      while (span_end < len(file_lines) and
                 file_lines[span_end].type == _IMPORT_CONTINUATION_RE):
        span_end += 1
      for i in xrange(span_begin, span_end):
        file_lines[i].move_span = (span_begin, span_end)


def _LinesAreAllBlank(file_lines, start_line, end_line):
  """Returns true iff all lines in [start_line, end_line) are blank/deleted."""
  for line_number in xrange(start_line, end_line):
    if (not file_lines[line_number].deleted and
        file_lines[line_number].type != _BLANK_LINE_RE):
      return False
  return True


def _CalculateReorderSpans(file_lines):
  """Fills each input_line's reorder_span field.

  A 'reorder span' is a range of lines (from file_lines) that only has
  imports in it, and maybe blank lines, and maybe associated
  comments.  In particular, it does not include any "real code"
  besides imports: no functions, no other variable assignment, no
  nothing.  We are willing to reorder imports freely inside a reorder
  span.

  Calculating reorder_span is easy: they're just the union of
  contiguous move-spans (with perhaps blank lines and comments
  thrown in), because move-spans share the 'no actual code'
  requirement.

  For lines of type _IMPORT_RE, the reorder span is set to the tuple
  [start_of_span, end_of_span).  All other lines have an arbitrary
  value for the reorder span.

  Arguments:
    file_lines: an array of LineInfo objects with .type and .move_span
       fields filled in.

  """
  # Happily, move_spans are disjoint. Just make sure they're sorted and unique.
  move_spans = [s.move_span for s in file_lines if s.move_span is not None]
  sorted_move_spans = sorted(set(move_spans))

  i = 0
  while i < len(sorted_move_spans):
    reorder_span_start = sorted_move_spans[i][0]

    # Add in the next move span if we're connected to it only by blank
    # lines.
    while i < len(sorted_move_spans) - 1:
      move_span_end = sorted_move_spans[i][1]
      next_move_span_start = sorted_move_spans[i + 1][0]
      if _LinesAreAllBlank(file_lines, move_span_end, next_move_span_start):
        i += 1
      else:
        break
    reorder_span_end = sorted_move_spans[i][1]
    # We'll map every line in the span to the span-extent.
    for line_number in xrange(reorder_span_start, reorder_span_end):
      file_lines[line_number].reorder_span = (reorder_span_start,
                                              reorder_span_end)
    i += 1


def ParseOneFile(file_contents, change_record):
  """Given a file object, read and classify the lines of the file.

  For each file that the change-record mentions, we return a list of
  LineInfo objects, which is a parsed version of each line, including
  not only its content but its 'type', its 'key', etc.

  Arguments:
    file_contents: a string containing the contents of the file
    change_record: the ChangeRecord struct for this source file.

  Returns:
     An array of LineInfo objects.  The first element is always a dummy
     element, so the first line of the file is at retval[1], matching
     the way humans count line numbers.

  """
  file_lines = _CalculateLineTypesAndKeys(file_contents, change_record)
  _CalculateMoveSpans(file_lines)
  _CalculateReorderSpans(file_lines)
  return file_lines


def _DeleteDuplicateLines(file_lines, line_ranges):
  """Goes through all lines in line_ranges, and if any are dups, deletes them.

  For all lines in line_ranges, if any is the same as a previously
  seen line, set its deleted bit to True.  (Ideally, line_ranges
  should include only 'top-level' lines.)

  We ignore lines that consist only of comments (or are blank).  We
  ignore end-of-line comments when comparing lines for equality.
  NOTE: Because our comment-finding RE is primitive, it's best if
  line_ranges covers only import lines.

  Arguments:
    file_lines: an array of LineInfo objects.
    line_ranges: a list of [start_line, end_line) pairs.
  """
  seen_lines = set()
  for line_range in line_ranges:
    for line_number in apply(xrange, line_range):
      if file_lines[line_number].type in (_BLANK_LINE_RE, _COMMENT_LINE_RE):
        continue
      uncommented_line = _COMMENT_RE.sub('', file_lines[line_number].line)
      if uncommented_line in seen_lines:
        file_lines[line_number].deleted = True
      elif not file_lines[line_number].deleted:
        seen_lines.add(uncommented_line)


def _DeleteExtraneousBlankLines(file_lines, line_range):
  """Deletes extraneous blank lines caused by line deletion.

  Here's a example file:
     import foo

     import bar

     import baz

  If we delete the "bar" line, we also want to delete one of
  the blank lines around it, otherwise we leave two blank lines
  between foo and baz which looks bad.  The idea is that if we have
  whitespace on both sides of a deleted span of code, the whitespace
  on one of the sides is 'extraneous'.  In this case, we should delete
  not only 'bar =' but also the whitespace line below it.  That
  leaves one blank line between Foo and Bar, like people would expect.

  We're careful to only delete the minimum of the number of blank
  lines that show up on either side.  If 'bar = ...' had one blank
  line before it, and one hundred after it, we'd only delete one blank
  line when we delete 'bar'.  This matches user's expecatations.

  The situation can get tricky when two deleted spans touch (we might
  think it's safe to delete the whitespace between them when it's
  not).  To be safe, we only do this check when an entire reorder-span
  has been deleted.  So we check the given line_range, and only do
  blank-line deletion if every line in the range is deleted.

  Arguments:
    file_lines: an array of LineInfo objects, with .type filled in.
    line_range: a range [start_line, end_line).  It should correspond
       to a reorder-span.
  """
  # First make sure the entire span is deleted.
  for line_number in apply(xrange, line_range):
    if not file_lines[line_number].deleted:
      return

  before_line = _PreviousNondeletedLine(file_lines, line_range[0])
  after_line = _NextNondeletedLine(file_lines, line_range[1] - 1)
  while (before_line and file_lines[before_line].type == _BLANK_LINE_RE and
         after_line and file_lines[after_line].type == _BLANK_LINE_RE):
    # OK, we've got whitespace on both sides of a deleted span.  We
    # only want to keep whitespace on one side, so delete on the other.
    file_lines[after_line].deleted = True
    before_line = _PreviousNondeletedLine(file_lines, before_line)
    after_line = _NextNondeletedLine(file_lines, after_line)


def _ShouldInsertBlankLine(decorated_move_span, next_decorated_move_span,
                           file_lines):
  """Returns true iff we should insert a blank line between the two spans.

  Given two decorated move-spans, of the form
     (reorder_range, kind, noncomment_lines, all_lines)
  returns true if we should insert a blank line between them.  We put
  a blank line when transitioning between system import's and
  third-party import's, and between third-party import's and other
  import's.

  If the two move spans are in different reorder_ranges, that means
  the first move_span is at the end of a reorder range.  In that case,
  a different rule for blank lines applies: if the next line is
  contentful (eg 'x = newmodule.whatever'), we want to insert a
  blank line to separate the move-span from the next block.  When
  figuring out if the next line is contentful, we skip over comments.

  Arguments:
    decorated_move_span: a decorated_move_span we may want to put a blank
       line after.
    next_decorated_move_span: the next decorated_move_span, which may
       be a sentinel decorated_move_span at end-of-file.
    file_lines: an array of LineInfo objects with .deleted filled in.

  Returns:
     true if we should insert a blank line after decorated_move_span.

  """
  # First handle the 'at the end of a reorder range' case.
  if decorated_move_span[0] != next_decorated_move_span[0]:
    next_line = _NextNondeletedLine(file_lines, decorated_move_span[0][1] - 1)
    # Skip over comments to figure out if the next line is contentful.
    while (next_line and next_line < len(file_lines) and
           file_lines[next_line].type == _COMMENT_LINE_RE):
      next_line += 1
    return (next_line and next_line < len(file_lines) and
            file_lines[next_line].type is None)

  # We never insert a blank line between two spans of the same kind.
  # Nor do we ever insert a blank line at EOF.
  (this_kind, next_kind) = (decorated_move_span[1],
                            next_decorated_move_span[1])
  if this_kind == next_kind or next_kind == _EOF_KIND:
    return False

  # Insert a blank line whenever the kind changes (third-party to
  # first-party or vice versa).  Kinds are defined below.
  return this_kind != next_kind


def _GetToplevelReorderSpans(file_lines):
  """Returns a sorted list of all reorder_spans.

  This routine looks at all the reorder_spans in file_lines and
  returns them in sorted order.

  Arguments:
    file_lines: an array of LineInfo objects with .type and
       .reorder_span filled in.

  Returns:
    A list of [start_line, end_line) reorder_spans.
  """
  return sorted(set([fl.reorder_span for fl in file_lines if fl.reorder_span]))


# These are potential 'kind' arguments to _FirstReorderSpanWith.
# We also sort our output in this order, to the extent possible.
_FUTURE_IMPORT_KIND = 1          # e.g. 'from __future__ import whatevs'
_SYSTEM_IMPORT_KIND = 2          # e.g. 'import os'
_THIRD_PARTY_IMPORT_KIND = 3     # e.g. 'import third_party.lint'
_FIRST_PARTY_IMPORT_KIND = 4     # e.g. 'import foo'
_EOF_KIND = 5                    # used at eof


def _CategorizePath(project_root):
  """Determine system and third-party modules from sys.path.

  This is based on the value of sys.path; we unfortunately have to guess at
  what is system vs. third-party vs. first-party.  We include all modules
  currently available; it may not match the list of system modules when your
  code (as opposed to when running this script) but should be close.  Returns a
  pair of frozensets (system modules, third-party modules).

  TODO(benkraft): This will ignore anything brought in by an import hook;
  hopefully those are all first-party or are for children of modules we
  classify correctly.
  TODO(benkraft): Make a better effort to use what we think the operand file's
  sys.path would be, rather than whatever ours happens to be.
  """
  try:
    # Super duper KA/webapp specific hack!  We need to do the same path-munging
    # appengine would do, so our path looks right.
    import appengine.tool_setup
    appengine.tool_setup.fix_sys_path()
  except Exception:
    pass

  # builtins don't show up in iter_modules, so we handle them specially.
  system_modules = set(sys.builtin_module_names)
  third_party_modules = set()

  for module_loader, name, ispkg in pkgutil.iter_modules():
    try:
      filename = module_loader.find_module(name).get_filename()
      path_parts = filename.split(os.sep)
    except Exception as e:
      # implementing get_filename() is not mandatory, so it may not work on
      # custom module loaders.  We just make some guesses, namely assuming that
      # the module name is kinda like a filename.
      print "WARNING: Couldn't determine filename for %s, got %s" % (name, e)
      filename = name
      path_parts = name.split('.')
    if name == 'argparse':
      # Annoying special case: the GAE sdk has its own copy of
      # argparse, making it seem like third-party code.
      system_modules.add(name)
    elif os.path.isabs(filename) and not filename.startswith(project_root):
      # An absolute, non-CWD-relative path.  If the directory looks like a
      # pip/virtualenv directory, it's a third-party module; otherwise it's
      # first-party.  Otherwise, it's hopefully system.
      if 'site-packages' in path_parts or 'dist-packages' in path_parts:
        third_party_modules.add(name)
      else:
        system_modules.add(name)
    elif 'shared' in path_parts or 'third_party' in path_parts:
      # If the directory is called "shared" or "third_party", we assume it's
      # some sort of vendored third-party thing, even though it's in the
      # current directory.  ("shared" being third-party is KA-specific.)
      third_party_modules.add(name)

  return frozenset(system_modules), frozenset(third_party_modules)


# Map from options.root to list of modules.  (The value they have
# depends on options.root.)
_SYSTEM_MODULES = {}
_THIRD_PARTY_MODULES = {}


def _GetLineKind(file_line, system_modules, third_party_modules):
  """Given a file_line + file being edited return best *_KIND value or None."""
  if file_line.deleted:
    return None
  if file_line.type not in (_IMPORT_RE, _IMPORT_CONTINUATION_RE):
    return None

  # _IMPORT_(CONTINUATION_)RE has key that starts with the module
  # being imported.  If multiple modules are imported on one import
  # line, we sort based on the first module listed.
  key = file_line.key.split(',')[0].strip()
  first_module = key.split(' ')[0].split('.')[0]
  if first_module == '__future__':
    return _FUTURE_IMPORT_KIND
  elif first_module in system_modules:
    return _SYSTEM_IMPORT_KIND
  elif first_module in third_party_modules:
    return _THIRD_PARTY_IMPORT_KIND
  return _FIRST_PARTY_IMPORT_KIND


def _FirstReorderSpanWith(file_lines, good_reorder_spans, kind,
                          system_modules, third_party_modules):
  """Returns [start_line,end_line) of 1st reorder_span with line of kind kind.

  This function iterates over all the reorder_spans in file_lines, and
  calculates the first one that has a line of the given kind in it.
  If no such reorder span is found, or if that reorder span comes
  after a 'contentful' line (since we want to insert new stuff at the
  top of the file), it takes the last span of 'lower' kinds
  (third-party is lowest, first-party is highest).  If no such reorder
  span is found, or if that reorder span comes after a 'contentful'
  line, it takes the first span of 'higher' kind.  If there's *still*
  no match, we return the first line past leading comments and
  whitespace.  If there's *still* no match, we just insert at
  end-of-file.

  Arguments:
    file_lines: an array of LineInfo objects with .type and
       .reorder_span filled in.
    good_reorder_spans: a sorted list of reorder_spans to consider
    kind: one of *_KIND values.
    system_modules, third_party_modules: from _CategorizePath().

  Returns:
    A pair of line numbers, [start_line, end_line), that is the 'best'
    reorder_span in file_lines for the given kind.

  """
  assert kind > 0 and kind < _EOF_KIND, kind

  # Find the first 'contentful' line so we can do that check later.
  first_contentful_line_num = 0
  while first_contentful_line_num < len(file_lines):
    if (file_lines[first_contentful_line_num].deleted or
        file_lines[first_contentful_line_num].type is not None):
      first_contentful_line_num += 1
    else:
      break

  # Let's just find the first and last span for each kind.  But
  # we ignore spans after the first 'contentful' line.
  first_reorder_spans = {}
  last_reorder_spans = {}
  for reorder_span in good_reorder_spans:
    if reorder_span[1] > first_contentful_line_num:
      continue
    for line_number in apply(xrange, reorder_span):
      line_kind = _GetLineKind(file_lines[line_number],
                               system_modules, third_party_modules)
      if line_kind is not None:
        first_reorder_spans.setdefault(line_kind, reorder_span)
        last_reorder_spans[line_kind] = reorder_span

  # Find the first span of our kind.
  if kind in first_reorder_spans:
    return first_reorder_spans[kind]

  # Second choice: last span of the kinds below us:
  for backup_kind in xrange(kind - 1, 0, -1):
    if backup_kind in last_reorder_spans:
      return last_reorder_spans[backup_kind]

  # Third choice: first span of the kinds above us.
  for backup_kind in xrange(kind + 1, _EOF_KIND):
    if backup_kind in first_reorder_spans:
      return first_reorder_spans[backup_kind]

  # There are no reorder-spans at all.  Return the first line past the
  # leading docstring comments, and whitespace.
  line_number = 0
  while line_number < len(file_lines):
    if (file_lines[line_number].deleted or
        file_lines[line_number].type == _BLANK_LINE_RE or
        file_lines[line_number].type == _DOCSTRING_COMMENT_RE):
      line_number += 1
    else:
      # Found a contentful line, let's go.
      return (line_number, line_number)

  # OK, I guess just insert at the end of the file
  return (len(file_lines), len(file_lines))


def _DecoratedMoveSpanLines(change_record, file_lines, move_span_lines,
                            system_modules, third_party_modules):
  """Given a span of lines from file_lines, returns a "decorated" result.

  First, we construct the actual contents of the move-span, as a list
  of strings (one per line).

  Second, we construct a string, of the 'contentful' part of the
  move_span -- that is, without the leading comments -- with
  whitespace removed, and a few other changes made.  This is used for
  sorting. (we remove whitespace so 'import foo' compares properly
  against 'import  bar')

  Third, we figure out the 'kind' of this span: first-party include,
  third-party include, etc.

  We return all of these together in a tuple, along with the
  reorder-span this move span is inside.  We pick the best
  reorder-span if one isn't already present (because it's a
  import we're adding in, for instance.)  This allows us to sort
  all the moveable content.

  Arguments:
    change_record: the ChangeRecord struct for this source file.
    file_lines: a list of LineInfo objects holding the parsed output of
      the file in change_record.filename
    move_span_lines: A list of LineInfo objects.  For import lines
      already in the file, this will be a sub-list of file_lines.  For
      import-lines we're adding in, it will be a newly created list.
    system_modules, third_party_modules: from _CategorizePath().

  Returns:
    A tuple (reorder_span, kind, sort_key, all_lines_as_list)
    sort_key is the 'contentful' part of the move_span, which is
      the import line (or first line of the import line if it spans
      multiple lines) with leading 'import ' or 'from ' removed.
    all_lines_as_list is a list of strings, not of LineInfo objects.
    Returns None if the move-span has been deleted, or for some other
      reason lacks a import line.
  """
  # Get to the first contentful line.
  for i in xrange(len(move_span_lines)):
    if (not move_span_lines[i].deleted and
        move_span_lines[i].type == _IMPORT_RE):
      first_contentful_line_num = i
      break
  else:       # for/else
    # No import line seen, must be a deleted span.
    return None

  firstline = move_span_lines[first_contentful_line_num]
  sort_key = firstline.line      # the import line itself

  # Get rid of the leading 'import' or 'from'; they are ignored when
  # sorting.
  if sort_key.startswith('import'):
    sort_key = sort_key[len('import'):].lstrip()
  if sort_key.startswith('from'):
    sort_key = sort_key[len('from'):].lstrip()

  all_lines = [li.line for li in move_span_lines]
  # Get rid of deleted lines
  all_lines = [l for (i, l) in enumerate(all_lines)
               if not move_span_lines[i].deleted]

  # Next figure out the kind (first-party import, third-party import, etc).
  kind = _GetLineKind(firstline, system_modules, third_party_modules)

  # All we're left to do is the reorder-span we're in.
  reorder_span = firstline.reorder_span
  if reorder_span is None:     # must be a new import we're adding
    # TODO(csilvers): could make this more efficient by storing, per-kind.
    toplevel_reorder_spans = _GetToplevelReorderSpans(file_lines)
    reorder_span = _FirstReorderSpanWith(file_lines, toplevel_reorder_spans,
                                         kind,
                                         system_modules, third_party_modules)

  return (reorder_span, kind, sort_key, all_lines)


def _DeleteLinesAccordingToChangeRecord(change_record, file_lines):
  """Deletes all lines that change_record tells us to, and cleans up after."""
  lines_to_delete = []

  # First, take the line-numbers the user asked for: the 'indexes' in
  # substrings_or_indexes_of_lines_to_delete.  We can tell because
  # they're ints.
  for i in change_record.substrings_or_indexes_of_lines_to_delete:
      if isinstance(i, int):           # s is an index, not a substring
        lines_to_delete.append(i)

  # Now take the 'substrings' in substrings_or_indexes_of_lines_to_delete
  # and find out what lines they go with.
  for (i, file_line) in enumerate(file_lines):
    for s in change_record.substrings_or_indexes_of_lines_to_delete:
      if not isinstance(s, int) and file_line.line and s in file_line.line:
        lines_to_delete.append(i)

  for line_number in lines_to_delete:
    # Delete the entire move-span (us and our preceding comments).
    for i in apply(xrange, file_lines[line_number].move_span):
      file_lines[i].deleted = True

  # Delete any duplicate lines in the input.
  toplevel_reorder_spans = _GetToplevelReorderSpans(file_lines)
  _DeleteDuplicateLines(file_lines, toplevel_reorder_spans)

  # If a whole reorder span was deleted, check if it has extra
  # whitespace on both sides that we could trim.
  for reorder_span in toplevel_reorder_spans:
    _DeleteExtraneousBlankLines(file_lines, reorder_span)


def FixFileLines(change_record, file_lines, flags):
  """Applies one block of lines from the input change-record info.

  Called once we have read all the lines from the input pertaining to
  a single source file, and parsed them into an change_record.  At
  that point we edit the source file, remove the old import's,
  insert new import's, and reorder the lot, all as specified by the
  change-record.  The resulting source code lines are returned.

  Arguments:
    change_record: a ChangeRecord object holding a subset of input to
      this script as it pertains to a single source file.
    file_lines: a list of LineInfo objects holding the parsed output of
      the file in change_record.filename
    flags: commandline flags, as parsed by optparse.  We use
       flags.safe_headers to turn off deleting lines, and
       flags.root to figure out first-party vs third-party modules.

  Returns:
    An array of 'fixed' source code lines, after modifications as
    specified by the change-record.
  """
  # We need to initialize the globals needed for _GetLineKind().
  if flags.root not in _SYSTEM_MODULES:
    _SYSTEM_MODULES[flags.root], _THIRD_PARTY_MODULES[flags.root] = (
      _CategorizePath(os.path.abspath(flags.root)))
  system_modules = _SYSTEM_MODULES[flags.root]
  third_party_modules = _THIRD_PARTY_MODULES[flags.root]

  # First delete any lines we should delete.
  if not flags.safe_headers:
    _DeleteLinesAccordingToChangeRecord(change_record, file_lines)

  # With these deletions, we may be able to merge together some
  # reorder-spans.  Recalculate them to see.
  _CalculateReorderSpans(file_lines)

  # For every move-span in our file -- that's every import we saw
  # -- 'decorate' the move-range to allow us to sort them.
  move_spans = set([fl.move_span for fl in file_lines if fl.move_span])
  decorated_move_spans = []
  for (start_line, end_line) in move_spans:
    decorated_span = _DecoratedMoveSpanLines(
      change_record, file_lines, file_lines[start_line:end_line],
      system_modules, third_party_modules)
    if decorated_span:
      decorated_move_spans.append(decorated_span)

  # Now let's add in a decorated move-span for all the new import's.
  for line in change_record.imports_to_add:
    # TODO(csilvers): break lines that are >80 chars
    line_infos = [LineInfo(line)]

    # Get the key for our new import
    m = _IMPORT_RE.match(line)
    assert m, line
    key = m.group(1)

    for li in line_infos:
      li.type = _IMPORT_CONTINUATION_RE    # will fix line_infos[0] up after
      li.key = key
    line_infos[0].type = _IMPORT_RE

    decorated_span = _DecoratedMoveSpanLines(
      change_record, file_lines, line_infos,
      system_modules, third_party_modules)
    assert decorated_span, 'line to add is not a import line?'
    decorated_move_spans.append(decorated_span)

  # Add a sentinel decorated move-span, to make life easy, and sort.
  decorated_move_spans.append(((len(file_lines), len(file_lines)),
                               _EOF_KIND, '', []))
  decorated_move_spans.sort()

  # Now go through all the lines of the input file and construct the
  # output file.  Before we get to the next reorder-span, we just
  # copy lines over verbatim (ignoring deleted lines, of course).
  # In a reorder-span, we just print the sorted content, introducing
  # blank lines when appropriate.
  output_lines = []
  line_number = 0
  while line_number < len(file_lines):
    current_reorder_span = decorated_move_spans[0][0]

    # Just copy over all the lines until the next reorder span.
    while line_number < current_reorder_span[0]:
      if not file_lines[line_number].deleted:
        output_lines.append(file_lines[line_number].line)
      line_number += 1

    # Now fill in the contents of the reorder-span from decorated_move_spans
    new_lines = []
    while (decorated_move_spans and
           decorated_move_spans[0][0] == current_reorder_span):
      new_lines.extend(decorated_move_spans[0][3])   # the full content
      if (len(decorated_move_spans) > 1 and
          _ShouldInsertBlankLine(decorated_move_spans[0],
                                 decorated_move_spans[1], file_lines)):
        new_lines.append('')
      decorated_move_spans = decorated_move_spans[1:]   # pop

    output_lines.extend(new_lines)
    line_number = current_reorder_span[1]               # go to end of span

  return output_lines


def GetFixedFile(change_record, flags):
  """Figure out import line fixes of one file.

  Given a change record for a single file, listing the import lines
  to add, remove, and re-sort, loads the file, makes the fixes, and
  returns the fixed file as a list of lines.  The flags affect the
  details of the fixing.

  Arguments:
    change_record: an ChangeRecord object holding the a subset of the
      change information as given on stdin, pertaining to a single
      source file.  change_record.filename indicates what file to edit.
    flags: commandline flags, as parsed by optparse.  We use
       flags.dry_run, and other flags indirectly.

  Returns:
    A list of strings representing the 'fixed' file, if the file has
    changed, or None if the file hasn't changed at all.

  """
  file_contents = _ReadFile(change_record.filename)
  if not file_contents:
    print '(skipping %s: not a readable file)' % change_record.filename
    return None
  print ">>> Fixing import lines in '%s'" % change_record.filename
  file_lines = ParseOneFile(file_contents, change_record)
  old_lines = [fl.line for fl in file_lines
               if fl is not None and fl.line is not None]
  fixed_lines = FixFileLines(change_record, file_lines, flags)
  fixed_lines = [line for line in fixed_lines if line is not None]
  if old_lines == fixed_lines:
    print "No changes in file", change_record.filename
    return None

  if flags.dry_run:
    PrintFileDiff(old_lines, fixed_lines)

  return fixed_lines


def FixManyFiles(change_records, flags):
  """Given a list of change_records, fix each file listed in the record.

  For each change-record in the input, which lists the import lines
  to add, remove, and re-sort, loads the file, makes the fixes, and
  writes the fixed file to disk.  The flags affect the details of the
  fixing.

  Arguments:
    change_records: a collection of ChangeRecord objects holding
      the parsed input.  Each ChangeRecord has information for a
      single file, with change_record.filename indicates what file
      to edit.
    flags: commandline flags, as parsed by optparse.  We use
       flags.dry_run, and other flags indirectly.

  Returns:
    The number of files fixed (as opposed to ones that needed no fixing).
  """
  file_and_fix_pairs = []
  for change_record in change_records:
    try:
      fixed_lines = GetFixedFile(change_record, flags)
      if not flags.dry_run and fixed_lines is not None:
        file_and_fix_pairs.append((change_record.filename, fixed_lines))
    except FixIncludesError, why:
      print 'ERROR: %s - skipping file %s' % (why, change_record.filename)

  for filename, fixed_lines in file_and_fix_pairs:
    _WriteFileContents(filename, fixed_lines)

  files_fixed = [filename for filename, _ in file_and_fix_pairs]

  print 'Edited %d files on your behalf.\n' % len(files_fixed)
  return len(files_fixed)


def ProcessInput(f, files_to_process, flags):
  """Fix the import lines as directed by f.

  Given a file object that has the changes to make (see top of file
  docstring for format), see every file to be edited and edit it,
  if appropriate.

  Arguments:
    f: an iterable object that holds the change information.
    files_to_process: A set of filenames, or None.  If not None, we
       ignore files mentioned in f that are not in files_to_process.
    flags: commandline flags, as parsed by optparse.  The only flag
       we use directly is flags.ignore_re, to indicate files not to
       process; we also pass the flags to other routines.

  Returns:
    The number of files that had to be modified (because they weren't
    already all correct).  In dry_run mode, returns the number of
    files that would have been modified.
  """
  # First collect all the change data from stdin.
  change_records = {}    # key is filename, value is a ChangeRecord
  while True:
    change_record_parser = ChangeRecordParser()
    try:
      change_record = change_record_parser.ParseOneRecord(f)
      if not change_record:
        break
    except FixIncludesError, why:
      print 'ERROR: %s' % why
      break
    filename = change_record.filename
    if files_to_process is not None and filename not in files_to_process:
      print '(skipping %s: not listed on commandline)' % filename
      continue
    if flags.ignore_re and re.search(flags.ignore_re, filename):
      print '(skipping %s: it matches --ignore_re, which is %s)' % (
          filename, flags.ignore_re)
      continue

    if filename in change_records:
      change_records[filename].Merge(change_record)
    else:
      change_records[filename] = change_record

  # Now ignore all the files that never had any contentful changes
  # seen for them.
  for filename in change_records:
    if not change_records[filename].HasContentfulChanges():
      print '(skipping %s: no contentful changes to make)' % filename
      # Mark that we're skipping this file by setting the record to None
      change_records[filename] = None

  # Now do all the fixing, and return the number of files modified
  contentful_records = [ior for ior in change_records.values() if ior]
  return FixManyFiles(contentful_records, flags)


def SortImportLinesInFiles(files_to_process, flags):
  """For each file in files_to_process, sort its import lines.

  This reads each input file, sorts the import lines lines, and
  replaces the input file with the result.  SortImportLinesInFiles
  does not add or remove any import line.

  Arguments:
    files_to_process: a list (or set) of filenames.
    flags: commandline flags, as parsed by optparse.  We do not use
       any flags directly, but pass them to other routines.

  Returns:
    The number of files that had to be modified (because they weren't
    already all correct, that is, already in sorted order).
  """
  sort_only_change_records = []
  for filename in files_to_process:
    # An empty change record has no adds or deletes, so its only effect
    # is to cause us to sort the import lines.
    sort_only_change_records.append(ChangeRecord(filename))
  return FixManyFiles(sort_only_change_records, flags)


def main(argv):
  # Parse the command line.
  parser = optparse.OptionParser(usage=_USAGE)
  parser.add_option('--safe_headers', action='store_true', default=True,
                    help=('Do not remove unused import lines from'
                          ' header files; just add new ones [default]'))
  parser.add_option('--nosafe_headers', action='store_false',
                    dest='safe_headers')

  parser.add_option('--root', default='.',
                    help=('The project-rootdir holding all the files you '
                          'are fixing. This is needed to determine what '
                          'imports are first-party vs third-party.'))

  parser.add_option('-s', '--sort_only', action='store_true',
                    help=('Just sort imports of files listed on cmdline;'
                          ' do not add or remove any'))

  parser.add_option('-n', '--dry_run', action='store_true', default=False,
                    help=('Do not actually edit any files; just print diffs.'
                          ' Return code is 0 if no changes are needed,'
                          ' else min(the number of files that would be'
                          ' modified, 127)'))

  parser.add_option('--ignore_re', default=None,
                    help=('Will skip editing any file whose'
                          ' name matches this regular expression.'))

  (flags, files_to_modify) = parser.parse_args(argv[1:])
  if files_to_modify:
    files_to_modify = set(files_to_modify)
  else:
    files_to_modify = None

  if flags.sort_only:
    if not files_to_modify:
      sys.exit('FATAL ERROR: -s flag requires a list of filenames')
    return SortImportLinesInFiles(files_to_modify, flags)
  else:
    return ProcessInput(sys.stdin, files_to_modify, flags)


if __name__ == '__main__':
  num_files_fixed = main(sys.argv)
  # rc's of 128 and above are reserved by the shell.
  sys.exit(min(num_files_fixed, 127))
