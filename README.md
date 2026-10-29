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

## Triângulo retângulo de Fermat e as assinaturas `(4a, 2b, 4c)`, `(2a, 4b, 4c)`

[`BealPrizeProof/RightTriangle.lean`](BealPrizeProof/RightTriangle.lean):

- `not_fermat_4m4 : b ≠ 0 → c ≠ 0 → a ^ 4 - b ^ 4 ≠ c ^ 2` (em `ℤ`), por descida infinita
  sobre `|a|` (o Mathlib só tem a equação irmã `not_fermat_42`, `a⁴ + b⁴ ≠ c²`);
- `not_fourth_add_sq_eq_fourth : x ≠ 0 → y ≠ 0 → x ^ 4 + y ^ 2 ≠ z ^ 4`;
- `noSolution_four_two_four`, `noSolution_two_four_four`: `A^x + B^y ≠ C^z` para `A, B > 0`
  quando `4 ∣ x, 2 ∣ y, 4 ∣ z` (resp. `2 ∣ x, 4 ∣ y, 4 ∣ z`), sem hipótese de coprimalidade;
- `signatureCase_of_four_two_four`, `signatureCase_of_two_four_four`: `SignatureCase x y z`
  nessas famílias. Exemplos: `(4, 2, 4)`, `(8, 2, 4)` (fora da faixa de Beal, `y = 2`),
  `(4, 6, 4)`, `(6, 4, 4)`, `(10, 4, 8)`.

O que **não** é: progresso em Beal. É matemática clássica de Fermat; nessas assinaturas a equação
não tem solução positiva e a conclusão vale por vacuidade. Junto com `(4a, 4b, 2c)` as três
posições do expoente "2" ficam cobertas, mas só quando os outros dois expoentes são múltiplos de 4.

Origem: ATK kernel, `ATK/FermatRightTriangle.lean` (`not_fermat_4m4` e a descida) e
`ATK/BealFermatDescent.lean` (`sem_solucao_424`, `sem_solucao_244`, `beal_424`, `beal_244`),
espelho público `atk-math-core-public/imports/M-Core/atk-kernel` (M-Core `390e378`).
Os demais corolários desse arquivo ATK (`√2`, número congruente 1) não foram portados: não
são sobre Beal.

Axiomas: `FermatM42` e `FermatM42.Minimal` usam `[propext]`; `FermatM42.neg_a` e
`isCoprime_sq_sub` usam `[propext, Quot.sound]`; todos os outros
`[propext, Classical.choice, Quot.sound]`.

## `A⁶ + B⁶ ≠ C²` (Euler, via FLT(3)) e a assinatura `(6a, 6b, 2c)`

[`BealPrizeProof/SixSixTwo.lean`](BealPrizeProof/SixSixTwo.lean):

- `sixth_add_sixth_ne_sq_of_coprime : 0 < A → 0 < B → Nat.Coprime A B → A ^ 6 + B ^ 6 ≠ C ^ 2`
  (tripla pitagórica primitiva `(A³, B³, C)`, fatores coprimos de um cubo são cubos, e
  `fermatLastTheoremThree` do Mathlib);
- `sixth_add_sixth_ne_sq : 0 < A → 0 < B → A ^ 6 + B ^ 6 ≠ C ^ 2`, **sem** coprimalidade: com
  `g = mdc(A, B)`, `g⁶ ∣ C²` dá `g³ ∣ C`, e dividindo por `g⁶` cai no caso coprimo;
- `noSolution_six_six_two`, `signatureCase_of_six_six_two`: `6 ∣ x, 6 ∣ y, 2 ∣ z`. Exemplos:
  `(6, 6, 2)` (fora da faixa de Beal), `(12, 6, 4)`, `(6, 6, 4)`, `(6, 12, 10)`, `(18, 6, 14)`.

Sobre a coprimalidade: o ATK (`dmSq_seis`) só prova o caso coprimo e trata `mdc(A, B) > 1` no
nível de Beal (`beal_662`: um primo comum de `A, B` divide `C`, via `primo_ab_divide_c`; aqui seria
`prime_dvd_C`). Este repositório faz a redução na própria equação, o que dá o enunciado mais forte
"sem solução positiva" e permite usar `signatureCase_of_noSolution`, como nas outras famílias.

O que **não** é: progresso em Beal; é Euler + FLT(3).

Origem: ATK kernel, `ATK/DarmonMerelSeis.lean` (`cubo`, `par_cubo`, `seis_impar`, `dmSq_seis`) e
`ATK/BealSeisSeisDois.lean` (`sem_solucao_662`, `beal_662`), mesmo espelho. A redução sem
coprimalidade (`sixth_add_sixth_ne_sq`) é nova aqui. Não portado: `darmonMerel_iff_reduzido`, que
fala da ponte condicional Darmon–Merel do ATK.

Axiomas: todos `[propext, Classical.choice, Quot.sound]`.

## Beal ⟺ nenhuma solução dois a dois coprima

[`BealPrizeProof/Pairwise.lean`](BealPrizeProof/Pairwise.lean):

- `statement_iff_pairwiseForm : BealPrize.Statement ↔ PairwiseForm`, em que `PairwiseForm` diz que
  não há solução com `A, B, C` dois a dois coprimos;
- `statement_iff_gcdOneForm : BealPrize.Statement ↔ GcdOneForm` (`mdc(A, B, C) = 1`);
- lemas de propagação: `prime_dvd_A`, `prime_dvd_B` (com o `prime_dvd_C` já existente, um primo
  que divide dois termos divide o terceiro), `coprime_AC_of_coprime_AB`,
  `coprime_BC_of_coprime_AB`, `coprimeForm_iff_pairwiseForm`.

O que **não** é: progresso. São reduções equivalentes do enunciado fixado.

Origem: ATK kernel, `ATK/BealReduction.lean` (`beal_iff_pairwise`, `primitive_iff_pairwise`,
`beal_iff_gcdOne`, `primo_*_divide_*`, `coprime_*_de_ab`), mesmo espelho. A prova de
`statement_iff_gcdOneForm` aqui é direta (o ATK passa por `GCDLowerBound`).

Axiomas: `PairwiseForm`, `GcdOneForm` usam `[propext]`; os demais
`[propext, Classical.choice, Quot.sound]`.

## Não portado

- A família com `d ∣ mdc(x, y, z)`, `d ∈ {5, 7, 11, 13, 17, 19}` (`ATK/BealFermatRegular.lean`):
  depende de FLT para primos regulares (`ATK/FltRegular`, derivado de `flt-regular`) e de
  certificados de número de classe (`ATK/FermatDezenove*`, etc.). Fica de fora.
- Os residuais "Beal ⟺ exclusão fora das famílias já cobertas" (`beal_iff_residual_descida`,
  `beal_iff_residual_seis`): dependem da cadeia `ATK.BealResidual`/`BealFourFourTwo`/`BealPartial`
  (filtros de `mdc` dos expoentes). São reformulações; não foram portados nesta rodada.

Regras: nenhum `sorry`, `axiom`, `native_decide` ou marcador; `#print axioms BealPrizeProof.main` fixado
com `#guard_msgs` quando `main` existir.

Prêmio: a formalização é material suplementar. O Clay e a AMS só consideram soluções publicadas
em periódico referado; o Clay espera ainda dois anos e aceitação geral.
