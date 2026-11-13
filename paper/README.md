# Consolidated paper

`main.tex` is the modular, consolidated version of the proof that synchronous majority on trees of
maximum degree four is P-complete. It is organised around monotone Boolean straight-line programs.

Build:

```sh
latexmk -pdf main.tex
```

Sections live in `sections/`. Appendix A maps every result to the original manuscript
(`../majority-trees-degree4-english.pdf`). Appendix B lists the audit notes.

The sanity-check scripts are in `../tools/check/`:

```sh
python3 -B ../tools/check/processor_sim.py 40   # processor, forced controls, all words phased
python3 -B ../tools/check/clock_sim.py 11       # timers, pulses, phase-defect generators, reader
```

They support the written proof but are not part of it.
