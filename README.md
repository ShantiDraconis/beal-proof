# Conjectura de Beal — prova (Lean 4 / Mathlib)

Depende do enunciado em [`ShantiDraconis/beal-statement`](https://github.com/ShantiDraconis/beal-statement),
fixado no commit `6fb9614`. O alvo é `BealPrize.Statement`, sem redefinição.

O prêmio Beal também vale para contraexemplo: `theorem main : ¬ BealPrize.Statement`.

Estado: sem prova. `OPEN_MATH = true`.

## Resultado parcial verificado: a diagonal (corolário de Fermat, não progresso em Beal)

[`BealPrizeProof/Diagonal.lean`](BealPrizeProof/Diagonal.lean):

- `diagonalCase_of_statement`: `DiagonalCase n` é a especialização de `BealPrize.Statement` a
  `x = y = z = n`. Fica ligado ao enunciado fixado, não a uma cópia.
- `diagonalCase_of_three_dvd`, `diagonalCase_of_four_dvd`: Beal vale na diagonal quando `3 ∣ n`
  ou `4 ∣ n`.

Por que não é progresso: nesses expoentes `A^n + B^n = C^n` não tem solução positiva
(`fermatLastTheoremThree`, `fermatLastTheoremFour`, já no Mathlib), então a conclusão de Beal vale
por vacuidade. O caso geral, com expoentes distintos, continua aberto.

| Declaração | Axiomas |
|---|---|
| `DiagonalCase` | `[propext]` |
| `diagonalCase_of_statement` | `[propext]` |
| `diagonalCase_of_fermat` | `[propext]` |
| `diagonalCase_of_three_dvd` | `[propext, Classical.choice, Quot.sound]` |
| `diagonalCase_of_four_dvd` | `[propext, Classical.choice, Quot.sound]` |

Fixados com `#guard_msgs` em [`BealPrizeProof/Audit.lean`](BealPrizeProof/Audit.lean).

Regras: nenhum `sorry`, `axiom`, `native_decide` ou marcador; `#print axioms BealPrizeProof.main` fixado
com `#guard_msgs` quando `main` existir.

Prêmio: a formalização é material suplementar. O Clay e a AMS só consideram soluções publicadas
em periódico referado; o Clay espera ainda dois anos e aceitação geral.
