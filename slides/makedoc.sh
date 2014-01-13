#!/bin/sh
SOURCES="Eq.v Num.v Singleton.v Power_mono.v reify.v Category.v" # euclid.v euclterm.v coq_euclid.v

for f in ${SOURCES}
do
  coqc $f
  coqdoc --latex --body-only --utf8 --interpolate $f
done

rm -f coqdoc.sty
