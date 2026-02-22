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
  my ($paren, $brace, $bracket) = (0, 0, 0);
  my @ch = split(//, $line);

  for (my $i = 0; $i < @ch; $i++) {
    my $x = $ch[$i];
    if    ($x eq '(') { $paren++; next; }
    elsif ($x eq ')') { $paren-- if $paren > 0; next; }
    elsif ($x eq '{') { $brace++; next; }
    elsif ($x eq '}') { $brace-- if $brace > 0; next; }
    elsif ($x eq '[') { $bracket++; next; }
    elsif ($x eq ']') { $bracket-- if $bracket > 0; next; }
    elsif ($x eq ':' && $paren == 0 && $brace == 0 && $bracket == 0) {
      my $lhs = substr($line, 0, $i);
      $lhs =~ s/^\s+//;
      $lhs =~ s/\s+$//;
      return -1 if $lhs eq q{};
      # Treat declaration heads as a single token; this avoids binder ':' in terms.
      return -1 if $lhs =~ /\s/;
      return $i;
    }
  }

  return -1;
}

sub is_ignored_start_line {
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
    next if is_ignored_start_line($start);

    my $colon = top_level_decl_colon_index($start);
    next if $colon < 0;

    my $after = substr($start, $colon + 1);
    next unless $after =~ /\S/;

    my ($lead) = $after =~ /^(\s*)/;
    my $hanging = $colon + 1 + length($lead // q{});

    my $base = leading_spaces($start);

    my @cont_idxs = ();
    # advance until we hit a non-declaration line
    for (my $j = $i + 1; $j < @lines; $j++) {
      my $ln = $lines[$j];
      last if leading_spaces($ln) <= $base || $ln =~ /=/;
      push @cont_idxs, $j;
    }
    next unless @cont_idxs;

    # Determine the base indent for the continuation block.
    # We'll keep the relative indent of continuation lines,
    #   so $delta is the only quantity we care in checking/applying fixes.
    my $start_ind = leading_spaces($lines[$cont_idxs[0]]);
    my $start_rel = $start_ind - $base;
    my $target = ($start_rel <= $hanging_threshold_rel && $start_ind < $hanging)
      ? ($base + $small_rel_indent)
      : $hanging;
    my $delta = $target - $start_ind;

    for my $j (@cont_idxs) {
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
