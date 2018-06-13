#!/bin/bash

cut -f 1-3 $1 | tail -n +2 | perl -ne 'BEGIN {my $sum = 0; my $iter = 0; } { my ($n, $t, $o) = split "\t"; my $diff = ($o - $t)/$t; print "$n $diff\n"; $sum += $diff; $iter += 1; } END { my $avg = $sum/$iter; print "# $avg\n"; }'
