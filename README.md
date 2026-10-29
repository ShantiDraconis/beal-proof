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

## Redução à forma coprima

[`BealPrizeProof/Reduction.lean`](BealPrizeProof/Reduction.lean): `statement_iff_coprimeForm`
prova que `BealPrize.Statement` equivale a "não há solução de `A^x + B^y = C^z` com `A`, `B`
coprimos e `x, y, z > 2`", que é a forma usada na literatura. Assim, um resultado publicado sobre
soluções coprimas pode ser aplicado diretamente ao enunciado fixado.

## Assinaturas que já seguem de Fermat (inclusive com expoentes distintos)

[`BealPrizeProof/Signatures.lean`](BealPrizeProof/Signatures.lean):
- `signatureCase_of_three_dvd`: Beal vale em `(x, y, z)` quando `3` divide os três expoentes,
  por exemplo `(3, 6, 9)`;
- `signatureCase_of_four_four_two`: Beal vale quando `4 ∣ x`, `4 ∣ y` e `2 ∣ z`, por exemplo
  `(4, 8, 6)`, via `not_fermat_42`.

Nessas assinaturas a equação não tem solução positiva, então a conclusão vale por vacuidade.
São corolários de Fermat, não progresso no caso geral.

Axiomas: `CoprimeForm`, `SignatureCase`, `signatureCase_of_statement` e
`signatureCase_of_noSolution` usam só `[propext]`; os demais usam
`[propext, Classical.choice, Quot.sound]`. Tudo fixado em `BealPrizeProof/Audit.lean`.

Regras: nenhum `sorry`, `axiom`, `native_decide` ou marcador; `#print axioms BealPrizeProof.main` fixado
com `#guard_msgs` quando `main` existir.

Prêmio: a formalização é material suplementar. O Clay e a AMS só consideram soluções publicadas
em periódico referado; o Clay espera ainda dois anos e aceitação geral.
