#!/usr/bin/env python

##===-------- base.py - base, language-agnostic include-rewriter ----------===##
#
#                     The LLVM Compiler Infrastructure
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
##===----------------------------------------------------------------------===##

"""
This file defines the base FixIncludes class, that language-specific
classes (FixCppIncludes, FixPythonImports, etc) can derive from.
It has the main functionality for adding, removing, and reordering
includes, using regexps and helper functions that subclasses have
to define.

FixIncludes does its work in four stages.  In the first, it groups
physical lines together to form 'move spans'.  A 'move span' is the
atomic unit for moving or deleting code.  For instance, for C++ a move
span is either a) an #include line, along with any comment lines
immediately preceding it; b) a forward-declare line -- or more if it's
a multi-line forward declare -- along with preceding comments; c) any
other single line.  Example:

   // I really am glad I'm forward-declaring this class!
   // If I didn't, I'd have to #include the entire world.
   template<typename A, typename B, typename C, typename D>
   class MyClass;

Then, it groups move spans together into 'reorder spans'.  These are
spans of code that consist entirely of move-spans, maybe separated by
blank lines and comments.  We assume that we can arbitrarily reorder
#includes and forward-declares within a reorder span, without
affecting correctness.  Things like #ifdefs, #defines, namespace
declarations, static variable declarations, class definitions, etc --
just about anything -- break up reorder spans.

In stage 3 it does all the deletions that it is told to delete:
removing all #include and forward-declare lines, say.

In stage 4 it adds all the new #includes and forward-declares it is
told to add.  Then it reorders the #includes and forward-declares
within each reorder-span to match the canonical order.  Each subclass
defines its own order.

All this moving messes up the blank lines, which we then need to fix
up.  Then we're done!
"""

__author__ = 'csilvers@khanacademy.org (Craig Silverstein)'

import collections
import difflib
import optparse
import os
import pipes  # For (undocumented) pipes.quote
import re
import sys
import subprocess


# Adapt Python 2 iterators to Python 3 syntax
if sys.version_info[0] < 3:
    def next(i):
        return i.next()


class FixIncludesError(Exception):
    pass


class FixIncludes(object):
    """The base class for fixing includes.  Subclasses must define much."""

    # A list of all known extensions for should be rewritten using
    # this subclass.  This is used to automatically discover the
    # correct fix-includes subclass to use for a given file.
    SOURCE_EXTENSIONS = []

    # These regexps are used to label each line of the source file.
    # Each regexp is evaluated in order, and the first one to match
    # defines the line.  If no regexp matches, the line will have type
    # None, meaning it's not include related.  All regexps are matched
    # using re.match(), so if you want to match something that's *not*
    # pinned to the beginning of the line, start it with `.*`.
    #
    # Subclasses should augment this list with the following, at least:
    #
    # * one_line_comment:
    #   Matches newline-terminated comments, including preceding
    #   whitespace.  The part of the line before the comment should
    #   also be matched, inside parens.
    #      re.compile(r'(.*?)\s*//.*')
    #
    # * multiline_comment_start, multiline_comment_end:
    #   Matches the start and end of multi-line comments. The start
    #   should include preceding whitespace.  The end should include
    #   trailing whitespace, *plus* the remainder of the line, which
    #   it should put in parens (note the start should *not* include
    #   text before the comment: our code only works on multi-line
    #   comments that start at the beginning of the line):
    #      re.compile(r'\s*/\*')
    #      re.compile(r'\*/\s*(.*)$')
    #
    # * include_line:
    #   Matches the 'include' (or import, or require, or...) line.
    #   Should include the unique "key" identifying this include in
    #   parens.  The "key" must fulfill these two requirements:
    #      1) If two includes are different, their keys are different.
    #      2) You can sort the includes based only on the key contents.
    #
    # * barrier_includes:  [optional]
    #   Matches include-lines that should be a barrier for sorting --
    #   that is, we should never reorganize the code so an #include
    #   that used to come before this line now comes after, or vice
    #   versa.  This can be used for 'fragile' #includes that require
    #   other #includes to happen before them to function properly.
    #   (Note that the barrier has no effect on where new #includes
    #   are added; it just affects the reordering of existing
    #   #includes.)
    #
    LINE_TYPES = collections.OrderedDict([
        ('blank_line', re.compile(r'\s*$')),
    ])

    # These functions are used to categorize include lines for sorting
    # purposes.  For instance, for C++ we want to put C system
    # includes (#include <stdio.h>) before C++ system includes
    # (#include <iostream>) before project includes (#include
    # "foo.h").  Other languages likewise divide their includes into
    # categories.  This list defines the include-categories as a list
    # of functions, ordered the way you want them to be ordered in the
    # output (so the function for C-system-includes would come first,
    # then the function for C++-system-includes, then project
    # includes.)
    # Each function takes a FileLine, and returns True if that FileLine
    # is an include-line that falls into this category.
    INCLUDE_CATEGORIES = collections.OrderedDict([
        # This default categorization puts all include-lines together.
        ('include_line', lambda line_info: line_info.type == 'include_line'),
        # TODO(csilvers): support project-includes here?  (via project_re?)
    ])

    def __init__(self, filename, file_contents):
        """Set up a FixIncludes object to fix up includes for one file.

        Arguments:
            filename: the name of the file.  Should be relative to some
                project-root.  Used just to determine sort order in some
                cases (e.g. for grouping includes by "project"), can be
                None if you don't care about such sorting.
            file_contents: the contents of the file to fix includes for.
        """
        self.filename = filename
        self.file_lines = self.calculate_file_lines(file_contents.splitlines())

    def calculate_line_types_and_keys_and_categories():
        """Fill file_line's type, is_first_line_of_this_type, and key fields.

        We match each line (line_info.line) against every regexp in
        LINE_TYPESS, and assign the first that matches, or None if
        none does.  We then set file_line.type and
        file_line.is_first_line_of_this_type for each file_line in
        file_lines.  For include-lines, we also set up the key and the
        include-category, which is used for sorting and grouping
        include-lines.

        Before this is called, self.file_lines must have all the .line fields
        filled in (luckily, this happens in the constructor.)
        """
        seen_types = set()
        in_multiline_comment = False
        for line_info in self.file_lines:
            if line_info.line is None:
                line_info.type = None
            elif _MULTILINE_COMMENT_START_RE.match(line_info.line):
                # Note: _MULTILINE_COMMENT_START_RE only matches a
                # comment at the start of a line.  Comments in the
                # middle of a line are ignored.  This can cause
                # problems with multi-line comments that start in the
                # middle of the line, but that's hopefully quite rare.
                # TODO(csilvers): check for that case.
                m = _MULTILINE_COMMENT_END_RE.match(line_info.line)
                if not m:             # comment continues onto future lines.
                    # We collapse multi-line comments into a
                    # bunch of one-line comments.
                    line_info.type = 'one_line_comment'
                    in_multiline_comment = True
                elif not m.group(1):  # comment is just this line
                    line_info.type = 'one_line_comment'
                else:                 # comment takes only part of line
                    # We treast partial comment-lines as content.
                    # TODO(csilvers): this mis-diagnoses lines like
                    #                 '/*comment*/class Foo;'
                    line_info.type = None
            elif (in_multiline_comment and
                  _MULTILINE_COMMENT_END_RE.match(line_info.line)):
                line_info.type = 'one_line_comment'
                in_multiline_comment = False
            elif in_multiline_comment:
                line_info.type = 'one_line_comment'
            else:
                for (line_type, type_re) in LINE_TYPESS.iteritems():
                    m = type_re.match(line_info.line)
                    if m:
                        line_info.type = line_type
                        if line_type == 'include_line':
                            line_info.key = m.group(1)
                        for (name, fn) in self.INCLUDE_CATEGORIES.iteritems():
                            if fn(line_info):
                                line_info.category = name
                                break
                        break
                else:    # for/else
                    line_info.type = None   # didn't match any re

            line_info.is_first_line_of_this_type = (
                line_info.type not in seen_types)
            seen_types.add(line_info.type)

    def calculate_move_spans(self):
      """Fills file_lines's move_span fields.

      A 'move span' is a range of lines (from file_lines) that
      includes an include-line, and all the comments preceding it.  It
      is the unit we would move if we decided to move (or delete) this
      include.

      For lines of type 'include_line', the move span is set to the
      tuple [start_of_span, end_of_span).  All other lines have the
      move span kept at None.

      Before this is called, self.file_lines must have all the .type fields
      filled in.
      """
      for line_number in range(len(self.file_lines)):
          if self.file_lines[line_number].type == 'include_line':
              span_begin = _line_number_starting_preceding_comments(
                  self.file_lines, line_number)
              for i in range(span_begin, line_number + 1):
                  self.file_lines[i].move_span = (span_begin, line_number + 1)

    def calculate_reorder_spans(self):
      """Fills file_lines's reorder_span fields.

      A 'reorder span' is a range of lines (from file_lines) that only
      has include-lines in it (and maybe blank lines, and comments
      associated with include-lines).  In particular, it does not
      include any "real code" besides includes: no functions, no
      static variable assignment, no macro #defines, no nothing.  We
      are willing to reorder include-lines freely inside a reorder
      span.

      Calculating reorder_span is easy: they're just the union of
      contiguous move-spans (with perhaps blank lines and comments
      thrown in), because move-spans share the 'no actual code'
      requirement.

      There's one exception: if any move-span matches the
      'barrier_includes', it means that we should consider that
      move-span to be a 'barrier': nothing should get reordered from
      one side of that move-span to the other.  (This is used for
      #includes that depend on other #includes being before them to
      function properly.)  We do that by putting them into their own
      reorder span.

      For lines of type 'include_line', the reorder span is set to the
      tuple [start_of_span, end_of_span).  All other lines have their
      reorder-span set to None.

      Before this is called, self.file_lines must have all the .type
      and .move_span fields filled in.
      """
      # Happily, move_spans are disjoint. Just sort and uniquify them.
      move_spans = [s.move_span for s in self.file_lines
                    if s.move_span is not None]
      sorted_move_spans = sorted(set(move_spans))

      i = 0
      while i < len(sorted_move_spans):
          reorder_span_start = sorted_move_spans[i][0]

          # If we're a 'nosort' include, we're always in a reorder
          # span of our own.  Otherwise, add in the next move span if
          # we're connected to it only by blank lines.
          if not self._contains_barrier_include(sorted_move_spans[i]):
              while i < len(sorted_move_spans) - 1:
                  move_span_end = sorted_move_spans[i][1]
                  next_move_span_start = sorted_move_spans[i+1][0]
                  if (_lines_are_all_blank(
                          self.file_lines, move_span_end, next_move_span_start)
                      and not self._contains_barrier_include(
                          sorted_move_spans[i+1])):
                      i += 1
                  else:
                      break

          reorder_span_end = sorted_move_spans[i][1]

          # We'll map every line in the span to the span-extent.
          for line_number in range(reorder_span_start, reorder_span_end):
              self.file_lines[line_number].reorder_span = (reorder_span_start,
                                                           reorder_span_end)
          i += 1

    def calculate_file_lines(self, f):
        """Given a file object, read and classify the lines of the file.

        Sets self.file_lines to be a list of LineInfo objects, which
        is a parsed version of each line, including not only its
        content but its 'type', its 'key', etc.

        Arguments:
          f: an iterable object returning lines from a file, with the
              line-ending ('\n', '\r\n', etc) omitted.
        """
        self.file_lines = [LineInfo(None, self.filename)]
        for line in f:
            self.file_lines.append(LineInfo(line, self.filename))
        self.calculate_line_types_and_keys_and_categories()
        self.calculate_move_spans()
        self.calculate_reorder_spans()

    def get_toplevel_reorder_spans(self):
        """Return a sorted list of all reorder_spans at the "top level".

        A top-level reorder span is one that is not inside a function
        definition, or an #ifdef, or a C++ namespace, etc.
        Intuitively, it's one where all the lines are unindented.

        This naive implementation just assumes we stop being at
        the top level as soon as we see a "contentful" line.
        Subclasses will probably want to be more clever.

        Before this is called, self.file_lines must have .type and
        .reorder_span filled in.

        Returns:
          A list of [start_line, end_line) reorder_spans.
        """
        first_contentful_line = 1
        for first_contentful_line in range(1, len(self.file_lines)):
            if self.file_lines[first_contentful_line].type is None:
                break

        reorder_spans = [fl.reorder_span for fl in self.file_lines
                         if fl.reorder_span]
        reorder_spans = sorted(set(reorder_spans))
        good_reorder_spans = []
        for reorder_span in reorder_spans:
            if reorder_span[-1] < first_contentful_line:
                good_reorder_spans.append(reorder_span)

        return good_reorder_spans

    def _contains_barrier_include(self, line_range):
        """True iff some line in [line_range[0], line_range[1]) is BARRIER."""
        barrier_re = self.LINE_TYPESS.get('barrier_includes')
        if not barrier_re:
            return False
        for line_number in range(*line_range):
            if (not self.file_lines[line_number].deleted and
                   barrier_re.match(file_lines[line_number].line)):
                return True
        return False

    def _delete_duplicate_lines(self, line_ranges):
        """Goes through all lines in line_ranges, and deletes any dups seen.

        For all lines in line_ranges, if any is the same as a
        previously seen line, set its deleted bit to True.  The
        purpose of line_ranges is to avoid lines in #ifdefs, say, that
        may be identical syntactically but have different semantics.
        Ideally, line_ranges should include only 'top-level' lines.

        We ignore lines that consist only of comments (or are blank).
        We ignore end-of-line comments when comparing lines for
        equality.  NOTE: Because our comment-finding RE is primitive,
        it's best if line_ranges covers only include-lines.  In
        particular, it should not cover lines that may have literal
        strings in them that could match comment-re.

        Arguments:
          line_ranges: a list of [start_line, end_line) pairs.
        """
        comment_re = self.LINE_TYPES['one_line_comment']
        seen_lines = set()
        for line_range in line_ranges:
            for line_number in range(*line_range):
                if self.file_lines[line_number].type in ('blank_line',
                                                         'one_line_comment'):
                    continue
                # The paren-group is everything before the comment.
                uncommented_line = comment_re.sub(
                    r'\1', self.file_lines[line_number].line)
                if uncommented_line in seen_lines:
                    self.file_lines[line_number].deleted = True
                elif not self.file_lines[line_number].deleted:
                    seen_lines.add(uncommented_line)

    def _first_reorder_span_with_category(self, good_reorder_spans, category):
        """[start_line, end_line) of first reorder_span with a given category.

        This function iterates over all the "good" reorder_spans in
        self.file_lines, and calculates the first one that has an
        include-line of the given category in it.  If no such reorder
        span is found, it takes the last span of 'lower' categories --
        that is, ones that come before it in INCLUDE_CATEGORIES.  If
        no such reorder span is found, it takes the first span of
        'higher' category.  If there's *still* no match, we return the
        first line past leading comments and whitespace.  If there's
        *still* no match, we just insert at end-of-file.

        Arguments:
          good_reorder_spans: a sorted list of reorder_spans to consider
             (should only include reorder_spans at the top level, not
             those inside functions or what-not).
          category: one of the keys from INCLUDE_CATEGORIES.

        Returns:
          A pair of line numbers, [start_line, end_line), that is the 'best'
          reorder_span in self.file_lines for the given category.
        """
        assert category in self.INCLUDE_CATEGORIES, category

        # Figure out where the first 'contentful' line is (after the
        # first 'good' span, so we skip past header guards and the
        # like).  Basically, the first contentful line is a line not
        # in any reorder span.
        for i in range(len(good_reorder_spans) - 1):
            if good_reorder_spans[i][1] != good_reorder_spans[i+1][0]:
                first_contentful_line = good_reorder_spans[i][1]
                break
        else:     # got to the end of the file without finding a break
            if good_reorder_spans:
                first_contentful_line = good_reorder_spans[-1][1]
            else:
                first_contentful_line = 0

        # Let's just find the first and last span for each category.
        first_reorder_spans = {}
        last_reorder_spans = {}
        for reorder_span in good_reorder_spans:
            for line_number in range(*reorder_span):
                category = self.file_lines[line_number].category
                if category is not None:
                    first_reorder_spans.setdefault(category, reorder_span)
                    last_reorder_spans[category] = reorder_span

        # Find the first span of *our* category.
        if category in first_reorder_spans:
          return first_reorder_spans[category]

        # Second choice: last span of the categories above us:
        all_categories = self.INCLUDE_CATEGORIES.keys()
        category_index = all_categories.index(category)
        for backup_category in range(category_index - 1, -1, -1):
            if backup_category in last_reorder_spans:
                return last_reorder_spans[backup_category]

        # Third choice: first span of the categories below us.
        for backup_category in range(category_index + 1, len(category_index)):
            if backup_category in first_reorder_spans:
                return first_reorder_spans[backup_category]

        # There are no reorder-spans at all.  Return the first line
        # past the leading comments and whitespace.
        line_number = 0
        while line_number < len(self.file_lines):
            if self.file_lines[line_number].deleted:
                line_number += 1
            elif self.file_lines[line_number].type == _BLANK_LINE_RE:
                line_number += 1
            elif self.file_lines[line_number].type == _COMMENT_LINE_RE:
                # We put #includes after top-of-file comments.
                line_number += 1
            else:
                return (line_number, line_number)

        # OK, I guess just insert at the end of the file.
        return (len(self.file_lines), len(self.file_lines))

    def _decorated_move_span_lines(move_span_lines,
                                   separate_project_includes):
        """Given a span of lines from file_lines, returns a "decorated" result.

        First, we construct the actual contents of the move-span, as a
        list of strings (one per line).

        Second, we construct a string of the 'contentful' part of the
        move_span -- that is, without any leading comments -- with
        whitespace collapsed, and a few other changes made.  This is
        used for sorting (we collapse whitespace so '# include <foo>'
        compares properly against '#include <bar>').

        Third, we figure out the 'category' of this span: system
        include, main-cu include, etc.

        We return all of these together in a tuple, along with the
        reorder-span this move span is inside.  We pick the best
        reorder-span if one isn't already present (because it's an
        #include we're adding in, for instance.)  This allows us to
        sort all the moveable content.

        Arguments:
          filename: the name of this IWYUOutputRecord struct for this source file.
          move_span_lines: A list of LineInfo objects.  For #includes and
            forward-declares already in the file, this will be a sub-list
            of file_lines.  For #includes and forward-declares we're adding
            in, it will be a newly created list.
          flags: commandline flags, as parsed by optparse.  We use
            flags.separate_project_includes to sort the #includes for the
            current project separately from other #includes.

  Returns:
    A tuple (reorder_span, category, sort_key, all_lines_as_list)
    sort_key is the 'contentful' part of the move_span, which whitespace
      removed, and -inl.h changed to _inl.h (so it sorts later).
    all_lines_as_list is a list of strings, not of LineInfo objects.
    Returns None if the move-span has been deleted, or for some other
      reason lacks an #include or forward-declare line.

        """
  # Get to the first contentful line.
  for i in range(len(move_span_lines)):
    if (not move_span_lines[i].deleted and
        move_span_lines[i].type in (_INCLUDE_RE, _FORWARD_DECLARE_RE)):
      first_contentful_line = i
      break
  else:       # for/else
    # No include or forward-declare line seen, must be a deleted span.
    return None

  firstline = move_span_lines[first_contentful_line]
  m = _INCLUDE_RE.match(firstline.line)
  if m:
    # If we're an #include, the contentful lines are easy.  But we have
    # to do the comment-replacing first.
    sort_key = firstline.line
    iwyu_version = iwyu_record.full_include_lines.get(m.group(1), '')
    if _COMMENT_LINE_RE.search(iwyu_version):  # the iwyu version has comments
      sort_key = iwyu_version                  # replace the comments
    all_lines = ([li.line for li in move_span_lines[:-1] if not li.deleted] +
                 [sort_key])
  else:
    # We're a forward-declare.  Also easy.
    contentful_list = [li.line for li in move_span_lines[first_contentful_line:]
                       if not li.deleted]
    sort_key = ''.join(contentful_list)
    all_lines = [li.line for li in move_span_lines if not li.deleted]

  # Get rid of whitespace in the contentful_lines
  sort_key = re.sub(r'\s+', '', sort_key)
  # Replace -inl.h with _inl.h so foo-inl.h sorts after foo.h in #includes.
  sort_key = sort_key.replace('-inl.h', '_inl.h')

  # Next figure out the kind.
  kind = _GetLineKind(firstline, iwyu_record.filename,
                      flags.separate_project_includes)

  # All we're left to do is the reorder-span we're in.  Hopefully it's easy.
  reorder_span = firstline.reorder_span
  if reorder_span is None:     # must be a new #include we're adding
    # If we're a forward-declare inside a namespace, see if there's a
    # reorder span inside the same namespace we can fit into.
    if kind == _FORWARD_DECLARE_KIND:
      (namespace_prefix, possible_reorder_span) = \
          _GetFirstNamespaceLevelReorderSpan(file_lines)
      if (namespace_prefix and possible_reorder_span and
          firstline.line.startswith(namespace_prefix)):
        # Great, we can go into this reorder_span.  We also need to
        # modify all-lines because this line doesn't need the
        # namespace prefix anymore.  Make sure we can do that before
        # succeeding.
        new_firstline = _RemoveNamespacePrefix(firstline.line, namespace_prefix)
        if new_firstline:
          assert all_lines[first_contentful_line] == firstline.line
          all_lines[first_contentful_line] = new_firstline
          reorder_span = possible_reorder_span

    # If that didn't work out, find a top-level reorder span to go into.
    if reorder_span is None:
      # TODO(csilvers): could make this more efficient by storing, per-kind.
      toplevel_reorder_spans = _GetToplevelReorderSpans(file_lines)
      reorder_span = _FirstReorderSpanWith(file_lines, toplevel_reorder_spans,
                                           kind, iwyu_record.filename, flags)

  return (reorder_span, kind, sort_key, all_lines)


class LineInfo(object):
        """Information about a single line of a source file."""
    def __init__(self, line, filename=None):
        """Initializes the content of the line, but no ancillary fields."""
        # The filename of the input file this line is part of (optional).
        self.filename = filename

        # The content of the line in the input file, with the
        # line-ending ('\n', '\r\n') removed.
        self.line = line

        # The 'type' of the line.  The 'type' is one of keys of
        # LINE_TYPESS, or None for any line that does not match any
        # regular expression in LINE_TYPESS.
        self.type = None

        # True if no lines processed before this one have the same type
        # as this line.
        self.is_first_line_of_this_type = False

        # Set to true if we want to delete/ignore this line in the
        # output (for instance, because the caller of the script says
        # to delete this line).  At the start, the only line to delete
        # is the 'dummy' line 0.
        self.deleted = self.line is None

        # If this line is an include-line, gives a [begin,end) pair
        # saying the 'span' this line is part of.  We do this for two
        # types of span: the move span (an #include or forward
        # declare, along with any preceding comments) and the reorder
        # span (a continguous block of move-spans, connected only by
        # blank lines and comments).  For lines that are not
        # include-lines, these may have an arbitrary value.
        self.move_span = None
        self.reorder_span = None

        # If this line is an include-line, gives the 'key' of the
        # line.  This is the parenthesized group in include_line.  For
        # C++ #includes, for instance, it is the filename included,
        # including the ""s or <>s.  For C++ forward-declare's it's
        # the name of the class/struct.  For non-include lines, this
        # is None.
        self.key = None

        # If this line is an include-line, gives the 'category' of
        # the line: system include, project include, etc.  Within
        # a reorder-span, we group includes by category, and also
        # use the category when sorting.
        self.category = None

    def __str__(self):
        if self.deleted:
            line = 'XX-%s-XX' % self.line
        else:
            line = '>>>%s<<<' % self.line
        return (
            '%s\n  -- type: %s (key: %s).  move_span: %s.  reorder_span: %s'
            % (line, self.type, self.key, self.move_span, self.reorder_span))


def _previous_nondeleted_line(file_lines, line_number):
    """Return the line number of the previous not-deleted line, or None."""
    for line_number in range(line_number - 1, -1, -1):
        if not file_lines[line_number].deleted:
            return line_number
    return None


def _next_nondeleted_line(file_lines, line_number):
    """Return the line number of the next not-deleted line, or None."""
    for line_number in range(line_number + 1, len(file_lines)):
        if not file_lines[line_number].deleted:
            return line_number
    return None


def _line_number_starting_preceding_comments(file_lines, line_number):
    """Return the linenum for the comment-lines preceding the given linenum.

    Looking at file_lines, look at the lines immediately preceding the
    given line-number.  If they're comment lines, return the first line
    of the comment lines preceding the given line.  Otherwise, return
    the given line number.

    As a special case, if the comments go all the way up to the first
    line of the file (line 1), we assume they're docstring lines, which
    are special -- they're not associated with any source code line --
    and we return line_number in that case.

    Arguments:
      file_lines: an array of LineInfo objects, with .type fields filled in.
      line_number: an index into file_lines.

    Returns:
      The first line number of the preceding comments, or line_number
        if there are no preceding comments or they appear to be a
        top-of-file docstring.
    """
    retval = line_number
    while retval > 0 and file_lines[retval - 1].type == _COMMENT_LINE_RE:
        retval -= 1
    if retval <= 1:            # top-of-line comments
        retval = line_number   # so ignore all the comment lines
    return retval


def _lines_are_all_blank(file_lines, start_line, end_line):
    """True iff all lines in [start_line, end_line) are blank/deleted."""
    for line_number in range(start_line, end_line):
        if (not file_lines[line_number].deleted and
                file_lines[line_number].type != 'blank_line'):
            return False
    return True


def _delete_extraneous_blank_lines(file_lines, line_range):
    """Deletes extraneous blank lines caused by line deletion.

    Here's a example file:
       class Foo { ... };

       class Bar;

       class Baz { ... }

    If we delete the "class Bar;" line, we also want to delete one of
    the blank lines around it, otherwise we leave two blank lines
    between Foo and Baz which looks bad.  The idea is that if we have
    whitespace on both sides of a deleted span of code, the whitespace
    on one of the sides is 'extraneous'.  In this case, we should delete
    not only 'class Bar;' but also the whitespace line below it.  That
    leaves one blank line between Foo and Bar, like people would expect.

    We're careful to only delete the minimum of the number of blank
    lines that show up on either side.  If 'class Bar' had one blank
    line before it, and one hundred after it, we'd only delete one blank
    line when we delete 'class Bar'.  This matches user's expecatations.

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
    for line_number in range(*line_range):
        if not file_lines[line_number].deleted:
            return

    before_line = _previous_nondeleted_line(file_lines, line_range[0])
    after_line = _next_nondeleted_line(file_lines, line_range[1] - 1)
    while (before_line and file_lines[before_line].type == 'blank_line' and
           after_line and file_lines[after_line].type == 'blank_line'):
      # OK, we've got whitespace on both sides of a deleted span.  We
      # only want to keep whitespace on one side, so delete on the other.
      file_lines[after_line].deleted = True
      before_line = _previous_nondeleted_line(file_lines, before_line)
      after_line = _next_nondeleted_line(file_lines, after_line)




def _ShouldInsertBlankLine(decorated_move_span, next_decorated_move_span,
                           file_lines, flags):
  """Returns true iff we should insert a blank line between the two spans.

  Given two decorated move-spans, of the form
     (reorder_range, kind, noncomment_lines, all_lines)
  returns true if we should insert a blank line between them.  We
  always put a blank line when transitioning from an #include to a
  forward-declare and back.  When the appropriate commandline flag is
  set, we also put a blank line between the 'main' includes (foo.h)
  and the C/C++ system includes, and another between the system
  includes and the rest of the Google includes.

  If the two move spans are in different reorder_ranges, that means
  the first move_span is at the end of a reorder range.  In that case,
  a different rule for blank lines applies: if the next line is
  contentful (eg 'static int x = 5;'), or a namespace start, we want
  to insert a blank line to separate the move-span from the next
  block.  When figuring out if the next line is contentful, we skip
  over comments.

  Arguments:
    decorated_move_span: a decorated_move_span we may want to put a blank
       line after.
    next_decorated_move_span: the next decorated_move_span, which may
       be a sentinel decorated_move_span at end-of-file.
    file_lines: an array of LineInfo objects with .deleted filled in.
    flags: commandline flags, as parsed by optparse.  We use
       flags.blank_lines, which controls whether we put blank
       lines between different 'kinds' of #includes.

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
            file_lines[next_line].type in (_NAMESPACE_START_RE, None))

  # We never insert a blank line between two spans of the same kind.
  # Nor do we ever insert a blank line at EOF.
  (this_kind, next_kind) = (decorated_move_span[1], next_decorated_move_span[1])
  if this_kind == next_kind or next_kind == _EOF_KIND:
    return False

  # We also never insert a blank line between C and C++-style #includes,
  # no matter what the flag value.
  if (this_kind in [_C_SYSTEM_INCLUDE_KIND, _CXX_SYSTEM_INCLUDE_KIND] and
      next_kind in [_C_SYSTEM_INCLUDE_KIND, _CXX_SYSTEM_INCLUDE_KIND]):
    return False

  # Handle the case we're going from an include to fwd declare or
  # back.  If we get here, we can't both be fwd-declares, so it
  # suffices to check if either of us is.
  if this_kind == _FORWARD_DECLARE_KIND or next_kind == _FORWARD_DECLARE_KIND:
    return True

  # Now, depending on the flag, we insert a blank line whenever the
  # kind changes (we handled the one case where a changing kind
  # doesn't introduce a blank line, above).
  if flags.blank_lines:
    return this_kind != next_kind

  return False


def _DecoratedMoveSpanLines(iwyu_record, file_lines, move_span_lines, flags):
  """Given a span of lines from file_lines, returns a "decorated" result.

  First, we construct the actual contents of the move-span, as a list
  of strings (one per line).  If we see an #include in the move_span,
  we replace its comments with the ones in iwyu_record, if present
  (iwyu_record will never have any comments if flags.comments is
  False).

  Second, we construct a string, of the 'contentful' part of the
  move_span -- that is, without the leading comments -- with
  whitespace removed, and a few other changes made.  This is used for
  sorting (we remove whitespace so '# include <foo>' compares properly
  against '#include <bar>').

  Third, we figure out the 'kind' of this span: system include,
  main-cu include, etc.

  We return all of these together in a tuple, along with the
  reorder-span this move span is inside.  We pick the best
  reorder-span if one isn't already present (because it's an
  #include we're adding in, for instance.)  This allows us to sort
  all the moveable content.

  Arguments:
    iwyu_record: the IWYUOutputRecord struct for this source file.
    file_lines: a list of LineInfo objects holding the parsed output of
      the file in iwyu_record.filename
    move_span_lines: A list of LineInfo objects.  For #includes and
      forward-declares already in the file, this will be a sub-list
      of file_lines.  For #includes and forward-declares we're adding
      in, it will be a newly created list.
    flags: commandline flags, as parsed by optparse.  We use
      flags.separate_project_includes to sort the #includes for the
      current project separately from other #includes.

  Returns:
    A tuple (reorder_span, kind, sort_key, all_lines_as_list)
    sort_key is the 'contentful' part of the move_span, which whitespace
      removed, and -inl.h changed to _inl.h (so it sorts later).
    all_lines_as_list is a list of strings, not of LineInfo objects.
    Returns None if the move-span has been deleted, or for some other
      reason lacks an #include or forward-declare line.
  """
  # Get to the first contentful line.
  for i in range(len(move_span_lines)):
    if (not move_span_lines[i].deleted and
        move_span_lines[i].type in (_INCLUDE_RE, _FORWARD_DECLARE_RE)):
      first_contentful_line = i
      break
  else:       # for/else
    # No include or forward-declare line seen, must be a deleted span.
    return None

  firstline = move_span_lines[first_contentful_line]
  m = _INCLUDE_RE.match(firstline.line)
  if m:
    # If we're an #include, the contentful lines are easy.  But we have
    # to do the comment-replacing first.
    sort_key = firstline.line
    iwyu_version = iwyu_record.full_include_lines.get(m.group(1), '')
    if _COMMENT_LINE_RE.search(iwyu_version):  # the iwyu version has comments
      sort_key = iwyu_version                  # replace the comments
    all_lines = ([li.line for li in move_span_lines[:-1] if not li.deleted] +
                 [sort_key])
  else:
    # We're a forward-declare.  Also easy.
    contentful_list = [li.line for li in move_span_lines[first_contentful_line:]
                       if not li.deleted]
    sort_key = ''.join(contentful_list)
    all_lines = [li.line for li in move_span_lines if not li.deleted]

  # Get rid of whitespace in the contentful_lines
  sort_key = re.sub(r'\s+', '', sort_key)
  # Replace -inl.h with _inl.h so foo-inl.h sorts after foo.h in #includes.
  sort_key = sort_key.replace('-inl.h', '_inl.h')

  # Next figure out the kind.
  kind = _GetLineKind(firstline, iwyu_record.filename,
                      flags.separate_project_includes)

  # All we're left to do is the reorder-span we're in.  Hopefully it's easy.
  reorder_span = firstline.reorder_span
  if reorder_span is None:     # must be a new #include we're adding
    # If we're a forward-declare inside a namespace, see if there's a
    # reorder span inside the same namespace we can fit into.
    if kind == _FORWARD_DECLARE_KIND:
      (namespace_prefix, possible_reorder_span) = \
          _GetFirstNamespaceLevelReorderSpan(file_lines)
      if (namespace_prefix and possible_reorder_span and
          firstline.line.startswith(namespace_prefix)):
        # Great, we can go into this reorder_span.  We also need to
        # modify all-lines because this line doesn't need the
        # namespace prefix anymore.  Make sure we can do that before
        # succeeding.
        new_firstline = _RemoveNamespacePrefix(firstline.line, namespace_prefix)
        if new_firstline:
          assert all_lines[first_contentful_line] == firstline.line
          all_lines[first_contentful_line] = new_firstline
          reorder_span = possible_reorder_span

    # If that didn't work out, find a top-level reorder span to go into.
    if reorder_span is None:
      # TODO(csilvers): could make this more efficient by storing, per-kind.
      toplevel_reorder_spans = _GetToplevelReorderSpans(file_lines)
      reorder_span = _FirstReorderSpanWith(file_lines, toplevel_reorder_spans,
                                           kind, iwyu_record.filename, flags)

  return (reorder_span, kind, sort_key, all_lines)


def _CommonPrefixLength(a, b):
  """Given two lists, returns the index of 1st element not common to both."""
  end = min(len(a), len(b))
  for i in range(end):
    if a[i] != b[i]:
      return i
  return end


def _NormalizeNamespaceForwardDeclareLines(lines):
  """'Normalize' namespace lines in a list of output lines and return new list.

  When suggesting new forward-declares to insert, iwyu uses the following
  format, putting each class on its own line with all namespaces:
     namespace foo { namespace bar { class A; } }
     namespace foo { namespace bar { class B; } }
     namespace foo { namespace bang { class C; } }
  We convert this to 'normalized' form, which puts namespaces on their
  own line and collects classes together:
     namespace foo {
     namespace bar {
     class A;
     class B;
     }  // namespace bar
     namespace bang {
     class C;
     }  // namespace bang
     }  // namespace foo

  Non-namespace lines are left alone.  Only adjacent namespace lines
  from the input are merged.

  Arguments:
    lines: a list of output-lines -- that is, lines that are ready to
       be emitted as-is to the output file.

  Returns:
    A new version of lines, with namespace lines normalized as above.
  """
  # iwyu input is very regular, which is nice.
  iwyu_namespace_re = re.compile(r'namespace ([^{]*) { ')
  iwyu_classname_re = re.compile(r'{ ([^{}]*) }')

  retval = []
  current_namespaces = []
  # We append a blank line so the final namespace-closing happens "organically".
  for line in lines + ['']:
    namespaces_in_line = iwyu_namespace_re.findall(line)
    differ_pos = _CommonPrefixLength(namespaces_in_line, current_namespaces)
    namespaces_to_close = reversed(current_namespaces[differ_pos:])
    namespaces_to_open = namespaces_in_line[differ_pos:]
    retval.extend('}  // namespace %s' % ns for ns in namespaces_to_close)
    retval.extend('namespace %s {' % ns for ns in namespaces_to_open)
    current_namespaces = namespaces_in_line
    # Now add the current line.  If we were a namespace line, it's the
    # 'class' part of the line (everything but the 'namespace {'s).
    if namespaces_in_line:
      m = iwyu_classname_re.search(line)
      if not m:
        raise FixIncludesError('Malformed namespace line from iwyu: %s', line)
      retval.append(m.group(1))
    else:
      retval.append(line)

  assert retval and retval[-1] == '', 'What happened to our sentinel line?'
  return retval[:-1]


def _DeleteLinesAccordingToIwyu(iwyu_record, file_lines):
  """Deletes all lines that iwyu_record tells us to, and cleans up after."""
  for line_number in iwyu_record.lines_to_delete:
    # Delete the entire move-span (us and our preceding comments).
    for i in range(*file_lines[line_number].move_span):
      file_lines[i].deleted = True

  while True:
    num_deletes = _DeleteEmptyNamespaces(file_lines)
    num_deletes += _DeleteEmptyIfdefs(file_lines)
    if num_deletes == 0:
      break

  # Also delete any duplicate lines in the input.  To avoid trouble
  # (accidentally deleting inside an #ifdef, for instance), we only
  # check 'top-level' #includes and forward-declares.
  toplevel_reorder_spans = _GetToplevelReorderSpans(file_lines)
  _DeleteDuplicateLines(file_lines, toplevel_reorder_spans)

  # If a whole reorder span was deleted, check if it has extra
  # whitespace on both sides that we could trim.  We've already
  # deleted extra blank lines inside #ifdefs and namespaces,
  # so looking at toplevel spans is enough.
  for reorder_span in toplevel_reorder_spans:
    _DeleteExtraneousBlankLines(file_lines, reorder_span)


def FixFileLines(iwyu_record, file_lines, flags):
  """Applies one block of lines from the iwyu output script.

  Called once we have read all the lines from the iwyu output script
  pertaining to a single source file, and parsed them into an
  iwyu_record.  At that point we edit the source file, remove the old
  #includes and forward-declares, insert the #includes and
  forward-declares, and reorder the lot, all as specified by the iwyu
  output script.  The resulting source code lines are returned.

  Arguments:
    iwyu_record: an IWYUOutputRecord object holding the parsed output
      of the include-what-you-use script (run at verbose level 1 or
      higher) pertaining to a single source file.
    file_lines: a list of LineInfo objects holding the parsed output of
      the file in iwyu_record.filename
    flags: commandline flags, as parsed by optparse.  We use
       flags.safe_headers to turn off deleting lines, and use the
       other flags indirectly (via calls to other routines).

  Returns:
    An array of 'fixed' source code lines, after modifications as
    specified by iwyu.
  """
  # First delete the includes and forward-declares that we should delete.
  # This is easy since iwyu tells us the line numbers.
  if not (flags.safe_headers and _MayBeHeaderFile(iwyu_record.filename)):
    _DeleteLinesAccordingToIwyu(iwyu_record, file_lines)

  # With these deletions, we may be able to merge together some
  # reorder-spans.  Recalculate them to see.
  _CalculateReorderSpans(file_lines)

  # For every move-span in our file -- that's every #include and
  # forward-declare we saw -- 'decorate' the move-range to allow us
  # to sort them.
  move_spans = set([fl.move_span for fl in file_lines if fl.move_span])
  decorated_move_spans = []
  for (start_line, end_line) in move_spans:
    decorated_span = _DecoratedMoveSpanLines(iwyu_record, file_lines,
                                             file_lines[start_line:end_line],
                                             flags)
    if decorated_span:
      decorated_move_spans.append(decorated_span)

  # Now let's add in a decorated move-span for all the new #includes
  # and forward-declares.
  symbol_names_seen = set()
  for line in iwyu_record.includes_and_forward_declares_to_add:
    line_info = LineInfo(line)
    m = _INCLUDE_RE.match(line)
    if m:
      line_info.type = _INCLUDE_RE
      line_info.key = m.group(1)
    else:
      # Avoid duplicates that can arise if different template args
      # were suggested by different iwyu analyses for this file.
      symbol_name = _GetSymbolNameFromForwardDeclareLine(line)
      if symbol_name in symbol_names_seen:
        continue
      symbol_names_seen.add(symbol_name)
      line_info.type = _FORWARD_DECLARE_RE
    decorated_span = _DecoratedMoveSpanLines(iwyu_record, file_lines,
                                             [line_info], flags)
    assert decorated_span, 'line to add is not an #include or fwd-decl?'
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
                                 decorated_move_spans[1], file_lines, flags)):
        new_lines.append('')
      decorated_move_spans = decorated_move_spans[1:]   # pop

    if not flags.keep_iwyu_namespace_format:
      # Now do the munging to convert namespace lines from the iwyu input
      # format to the 'official style' format:
      #    'namespace foo { class Bar; }\n' -> 'namespace foo {\nclass Bar;\n}'
      # along with collecting multiple classes in the same namespace.
      new_lines = _NormalizeNamespaceForwardDeclareLines(new_lines)
    output_lines.extend(new_lines)
    line_number = current_reorder_span[1]               # go to end of span

  return output_lines
def SortIncludesInFiles(files_to_process, flags):
  """For each file in files_to_process, sort its #includes.

  This reads each input file, sorts the #include lines, and replaces
  the input file with the result.  Like ProcessIWYUOutput, this
  requires that the file be writable, or that flags.checkout_command
  be set.  SortIncludesInFiles does not add or remove any #includes.
  It also ignores forward-declares.

  Arguments:
    files_to_process: a list (or set) of filenames.
    flags: commandline flags, as parsed by optparse.  We do not use
       any flags directly, but pass them to other routines.

  Returns:
    The number of files that had to be modified (because they weren't
    already all correct, that is, already in sorted order).
  """
  num_fixes_made = 0
  sort_only_iwyu_records = []
  for filename in files_to_process:
    # An empty iwyu record has no adds or deletes, so its only effect
    # is to cause us to sort the #include lines.  (Since fix_includes
    # gets all its knowledge of where forward-declare lines are from
    # the iwyu input, with an empty iwyu record it just ignores all
    # the forward-declare lines entirely.)
    sort_only_iwyu_records.append(IWYUOutputRecord(filename))
  return FixManyFiles(sort_only_iwyu_records, flags)


def main(argv):
  # Parse the command line.
  parser = optparse.OptionParser(usage=_USAGE)
  parser.add_option('-b', '--blank_lines', action='store_true', default=True,
                    help=('Put a blank line between primary header file and'
                          ' C/C++ system #includes, and another blank line'
                          ' between system #includes and google #includes'
                          ' [default]'))
  parser.add_option('--noblank_lines', action='store_false', dest='blank_lines')

  parser.add_option('--comments', action='store_true', default=False,
                    help='Put comments after the #include lines')
  parser.add_option('--nocomments', action='store_false', dest='comments')

  parser.add_option('--safe_headers', action='store_true', default=True,
                    help=('Do not remove unused #includes/fwd-declares from'
                          ' header files; just add new ones [default]'))
  parser.add_option('--nosafe_headers', action='store_false',
                    dest='safe_headers')

  parser.add_option('-s', '--sort_only', action='store_true',
                    help=('Just sort #includes of files listed on cmdline;'
                          ' do not add or remove any #includes'))

  parser.add_option('-n', '--dry_run', action='store_true', default=False,
                    help=('Do not actually edit any files; just print diffs.'
                          ' Return code is 0 if no changes are needed,'
                          ' else min(the number of files that would be'
                          ' modified, 100)'))

  parser.add_option('--ignore_re', default=None,
                    help=('fix_includes.py will skip editing any file whose'
                          ' name matches this regular expression.'))

  parser.add_option('--checkout_command', default=None,
                    help=('A command, such as "p4 edit", to run on all the'
                          ' non-writeable files before modifying them.  The'
                          ' filenames will be appended to the command after'
                          ' a space.  The command will not be run on any file'
                          ' that does not need to change.'))

  parser.add_option('--create_cl_if_possible', action='store_true',
                    default=True,
                    help=('If --checkout_command is "p4|g4|v4 edit" and'
                          ' all files to be modified needed to be checked out,'
                          ' then create a CL containing those files.'))
  parser.add_option('--nocreate_cl_if_possible', action='store_false',
                    dest='create_cl_if_possible')

  parser.add_option('--append_to_cl', action='store',
                    default=None, type='int', dest='append_to_cl',
                    help=('If provided, with a checkout_command, add files'
                          ' that need fixing to the specified existing CL.'))

  parser.add_option('--separate_project_includes', default=None,
                    help=('Sort #includes for current project separately'
                          ' from all other #includes.  This flag specifies'
                          ' the root directory of the current project.'
                          ' If the value is "<tld>", #includes that share the'
                          ' same top-level directory are assumed to be in the'
                          ' same project.  If not specified, project #includes'
                          ' will be sorted with other non-system #includes.'))

  parser.add_option('--invoking_command_line', default=None,
                    help=('Internal flag used by iwyu.py, It should be the'
                          ' command line used to invoke iwyu.py'))


  parser.add_option('-m', '--keep_iwyu_namespace_format', action='store_true',
                    default=False,
                    help=('Keep forward-declaration namespaces in IWYU format, '
                          'eg. namespace n1 { namespace n2 { class c1; } }.'
                          ' Do not convert to "normalized" Google format: '
                          'namespace n1 {\\nnamespace n2 {\\n class c1;'
                          '\\n}\\n}.'))
  parser.add_option('--nokeep_iwyu_namespace_format', action='store_false',
                    dest='keep_iwyu_namespace_format')

  (flags, files_to_modify) = parser.parse_args(argv[1:])
  if files_to_modify:
    files_to_modify = set(files_to_modify)
  else:
    files_to_modify = None

  if (flags.separate_project_includes and
      not flags.separate_project_includes.startswith('<') and  # 'special' vals
      not flags.separate_project_includes.endswith(os.path.sep) and
      not flags.separate_project_includes.endswith('/')):
    flags.separate_project_includes += os.path.sep

  if flags.append_to_cl and flags.create_cl_if_possible:
    sys.exit('FATAL ERROR: At most one of --append_to_cl and '
             '--create_cl_if_possible allowed')

  if flags.sort_only:
    if not files_to_modify:
      sys.exit('FATAL ERROR: -s flag requires a list of filenames')
    return SortIncludesInFiles(files_to_modify, flags)
  else:
    return ProcessIWYUOutput(sys.stdin, files_to_modify, flags)


if __name__ == '__main__':
  num_files_fixed = main(sys.argv)
  sys.exit(min(num_files_fixed, 100))
