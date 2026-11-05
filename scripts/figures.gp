# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
# gnuplot script called by scripts/figures.sh (variables b, out).
set terminal pngcairo size 1100,520 noenhanced font "DejaVu Sans,11"
set datafile separator whitespace
set grid lc rgb "#dddddd"
set key top left

set output out."/avx512_timings.png"
set title "CBQN baseline vs AVX-512 build: median wall time, 3 runs (identical stdout)"
set style data histograms
set style histogram clustered gap 1
set style fill solid 0.85 border -1
set ylabel "ms"
set yrange [0:*]
plot b."/timings.dat" using 2:xtic(1) title "baseline (0 zmm)" lc rgb "#4c72b0", \
     ""             using 3 title "AVX-512 (4557 zmm)" lc rgb "#dd8452", \
     ""             using ($0-0.17):($2):(sprintf("%d",$2)) with labels offset 0,0.7 notitle, \
     ""             using ($0+0.17):($3):(sprintf("%d",$3)) with labels offset 0,0.7 notitle
unset style
set style data points

set output out."/twin_trace_tokens.png"
set title "Forward (BOS) and twin (EOS) token per step, against torus phase 89t mod 2462"
set xlabel "torus phase"
set ylabel "token id"
set yrange [-10:520]
set xrange [0:2461]
set key outside right
plot b."/traces.tsv" using 2:4 with points pt 7 ps 0.6 lc rgb "#4c72b0" title "forward", \
     ""            using 2:($5+4) with points pt 6 ps 0.6 lc rgb "#c44e52" title "twin (+4 offset)"

set output out."/harmonic_scalars.png"
set title "Harmonic scalar cos(φ·π·x/2462) at every phase x = 0..2461 (CBQN values)"
set xlabel "x (phase)"
set ylabel "harmonic scalar"
set yrange [-1.05:1.05]
set key off
plot b."/traces.tsv" every ::0::2461 using 2:3 with points pt 7 ps 0.3 lc rgb "#55a868"

set output out."/tie_counts.png"
set title "Exact argmin ties per trace (7386 steps each)"
set style data histograms
set style fill solid 0.85 border -1
set xlabel ""
set ylabel "ties"
set yrange [0:4500]
set xrange [*:*]
plot b."/ties.dat" using 2:xtic(1) lc rgb "#8172b2" notitle, \
     ""          using 0:2:(sprintf("%d",$2)) with labels offset 0,0.7 notitle
unset style
set style data points

set output out."/snap_ties_cumulative.png"
set title "Midpoint snap: cumulative exact ties over 7386 steps"
set xlabel "step"
set ylabel "cumulative ties"
set autoscale
set yrange [0:*]
plot b."/traces.tsv" using 1:7 smooth cumulative lw 2 lc rgb "#8172b2"

set output out."/torus_path.png"
set title "Torus path from extract/torus_path.h: m mod 2462 against t for t = 0..4095, m = 89t, l = 2462t"
set xlabel "t"
set ylabel "m mod 2462"
set xrange [0:4095]
set yrange [0:2462]
plot b."/torus.dat" using 1:(int($2) % 2462) with points pt 7 ps 0.3 lc rgb "#4c72b0"
