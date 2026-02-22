#!/usr/bin/env perl
use strict;
use warnings;
use utf8;
use open qw(:std :encoding(UTF-8));
use List::Util 'max';

# Written primarily by Codex.
# Rule:
#   For each continuation line of a declaration type signature:
#   - compute hanging indent (first token position after ':', counting every Unicode code point as width 1)
#   - find the first continuation line indent `start`
#   - if `start` is <= +7 from declaration start and `start < hanging`, then set block start
#     to +6 relative to declaration start
#   - otherwise set block start to `hanging`
#   - apply the same delta to every line in the continuation block so internal indentation is preserved
# Example usage:
#   cd /workspace && ./scripts/agda-hanging-indent.pl --fix $(rg --files -g '*.agda')

my $mode = 'fix';
my @files;

while (@ARGV) {
  my $arg = shift @ARGV;
  if ($arg eq '--check') {
    $mode = 'check';
  } elsif ($arg eq '--fix') {
    $mode = 'fix';
  } else {
    push @files, $arg;
  }
}

die "usage: $0 [--check|--fix] <file...>\n" unless @files;

sub leading_spaces {
  my ($s) = @_;
  $s =~ /^(\s*)/;
  return length($1 // q{});
}

sub top_level_decl_colon_index {
  my ($line) = @_;
  # We want to find the colon in function definition but not anywhere else.
  #
  # For instance, we sometimes have colons in the middle of the reasoning block, such as
  #
  #     ((x : A) → Is-contr (B x))     ↔⟨ depfn-biimpl (λ x →
  #                                         equiv-then-contr-iff-contr (
  #                                           ≃-comm (Σ-≃-sections-at-base-center
  #                                             (x , recenter-contraction-at x a-is-contr)))) ⟩
  #     ((x : A) → Is-contr (Σ A B))   ↔⟨ (ev-pt ca , const) ⟩
  #
  # and in such cases we don't want to treat the first line as
  # a function declaration start line (it isn't!). So we consider lines that
  #
  #  - start with optional whitespace,
  #  - followed by a non-empty sequence of non-whitespace characters that
  #    does not contain (), [], {}, or =
  #  - followed by optional whitespaces
  #  - and finally a colon
  #
  # to be function declaration start lines, and then return the index of the colon in such lines.
  return -1 unless $line =~ /^(\s*[^()\[\]{}:=\s]+)(\s*):/;
  return length($1 . $2);
}

sub is_not_fn_declaration_start_line {
  my ($line) = @_;
  return 1 if $line =~ /^\s*$/;
  return 1 if $line =~ /^\s*--/;

  my $trim = $line;
  $trim =~ s/^\s+//;
  return 1 if $trim =~ /^(module|data|record|syntax|infix)\b/;
  return 1 if $line =~ /=/;

  return 0;
}

my %file_changes;
my $total_changes = 0;
my $total_hits = 0;
my $small_rel_indent = 6;
my $hanging_threshold_rel = 7;

for my $file (@files) {
  open my $fh, '<:encoding(UTF-8)', $file or die "open $file: $!";
  my @lines = <$fh>;
  chomp @lines;

  my $changed_in_current_file = 0;

  for (my $i = 0; $i < @lines; $i++) {
    my $start = $lines[$i];
    next if is_not_fn_declaration_start_line($start);

    my $colon = top_level_decl_colon_index($start);
    next if $colon < 0;

    my $after = substr($start, $colon + 1);
    next unless $after =~ /\S/;

    my ($lead) = $after =~ /^(\s*)/;
    my $hanging = $colon + 1 + length($lead // q{});

    my $base = leading_spaces($start);

    # Determine the range ([cont_start, cont_end_exclusive))
    #   to which the type declaration continues.
    my $cont_start = $i + 1;
    my $cont_end_exclusive = $cont_start;
    # advance until we hit a non-continuation line
    for (; $cont_end_exclusive < @lines; $cont_end_exclusive++) {
      my $ln = $lines[$cont_end_exclusive];
      last if leading_spaces($ln) <= $base || $ln =~ /=/;
    }
    next if $cont_end_exclusive == $cont_start;

    # Determine the base indent for the continuation block.
    # We'll keep the relative indent of continuation lines,
    #   so $delta is the only quantity we care in checking/applying fixes.
    my $start_ind = leading_spaces($lines[$cont_start]);
    my $start_rel = $start_ind - $base;
    my $target = ($start_rel <= $hanging_threshold_rel && $start_ind < $hanging)
      ? ($base + $small_rel_indent)
      : $hanging;
    my $delta = $target - $start_ind;

    for (my $j = $cont_start; $j < $cont_end_exclusive; $j++) {
      my $ln = $lines[$j];
      my $ind = leading_spaces($ln);
      my $expected = max($ind + $delta, 0);

      if ($ind != $expected) {
        $total_hits++;
        if ($mode eq 'fix') {
          $ln =~ s/^\s+//;
          $lines[$j] = (' ' x $expected) . $ln;
          $changed_in_current_file++;
          $total_changes++;
        } else {
          print "$file:" . ($j + 1) . ": expected indent $expected (base=$base, start=$start_ind, target_start=$target, delta=$delta, hanging=$hanging), found $ind | $ln\n";
        }
      }
    }

    # Skip continuation lines we just processed.
    $i = $cont_end_exclusive - 1;
  }

  if ($mode eq 'fix' && $changed_in_current_file > 0) {
    open my $out, '>:encoding(UTF-8)', $file or die "write $file: $!";
    print {$out} join("\n", @lines), "\n";
    close $out;
    $file_changes{$file} = $changed_in_current_file;
  }
}

if ($mode eq 'fix') {
  print "TOTAL_CHANGED $total_changes\n";
  for my $f (sort keys %file_changes) {
    print "$f $file_changes{$f}\n";
  }
} else {
  print "TOTAL_HITS $total_hits\n";
}
