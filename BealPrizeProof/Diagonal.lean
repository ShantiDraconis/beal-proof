import BealPrize
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

/-!
# Beal na diagonal `x = y = z` com `3 ∣ n` ou `4 ∣ n`

Resultado verdadeiro e verificado no kernel, mas **não é progresso no problema de Beal**: é um
corolário imediato do Último Teorema de Fermat para os expoentes 3 e 4, que já estão no Mathlib
(`fermatLastTheoremThree`, `fermatLastTheoremFour`). Nesses expoentes a equação
`A ^ n + B ^ n = C ^ n` não tem solução positiva, então a conclusão de Beal vale por vacuidade.

`BealPrize.Statement` continua aberto (`OPEN_MATH = true`).
-/

namespace BealPrizeProof

/-- O enunciado de Beal restrito à diagonal `x = y = z = n`. -/
def DiagonalCase (n : ℕ) : Prop :=
  ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C → A ^ n + B ^ n = C ^ n →
    ∃ p : ℕ, p.Prime ∧ p ∣ A ∧ p ∣ B ∧ p ∣ C

/-- `DiagonalCase n` é exatamente a especialização do enunciado fixado: quem provar
`BealPrize.Statement` prova todos os casos diagonais com `n > 2`. -/
theorem diagonalCase_of_statement (h : BealPrize.Statement) {n : ℕ} (hn : 2 < n) :
    DiagonalCase n :=
  fun A B C hA hB hC hE => h A B C n n n hA hB hC hn hn hn hE

/-- Onde Fermat vale para o expoente `n`, a diagonal de Beal vale por vacuidade. -/
theorem diagonalCase_of_fermat {n : ℕ} (h : FermatLastTheoremFor n) : DiagonalCase n :=
  fun A B C hA hB hC hE => absurd hE (h A B C hA.ne' hB.ne' hC.ne')

/-- Beal na diagonal quando `3 ∣ n`. -/
theorem diagonalCase_of_three_dvd {n : ℕ} (hn : 3 ∣ n) : DiagonalCase n :=
  diagonalCase_of_fermat (fermatLastTheoremThree.mono hn)

/-- Beal na diagonal quando `4 ∣ n`. -/
theorem diagonalCase_of_four_dvd {n : ℕ} (hn : 4 ∣ n) : DiagonalCase n :=
  diagonalCase_of_fermat (fermatLastTheoremFour.mono hn)

end BealPrizeProof
