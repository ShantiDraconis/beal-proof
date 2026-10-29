# Conjectura de Beal — prova (Lean 4 / Mathlib)

Depende do enunciado em [`ShantiDraconis/beal-statement`](https://github.com/ShantiDraconis/beal-statement),
fixado no commit `6fb9614`. O alvo é `BealPrize.Statement`, sem redefinição.

O prêmio Beal também vale para contraexemplo: `theorem main : ¬ BealPrize.Statement`.

Estado: sem prova. `OPEN_MATH = true`.

Regras: nenhum `sorry`, `axiom`, `native_decide` ou marcador; `#print axioms BealPrizeProof.main` fixado
com `#guard_msgs` quando `main` existir.

Prêmio: a formalização é material suplementar. O Clay e a AMS só consideram soluções publicadas
em periódico referado; o Clay espera ainda dois anos e aceitação geral.
