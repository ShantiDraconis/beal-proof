import BealPrize
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

/-!
# Assinaturas `(x, y, z)` em que Beal já segue de Fermat

Para uma assinatura fixa `(x, y, z)`, `SignatureCase x y z` é o enunciado de Beal restrito a
esses expoentes. Dois resultados do Mathlib cobrem famílias inteiras de assinaturas, inclusive
com expoentes distintos:

* `3 ∣ x`, `3 ∣ y`, `3 ∣ z`: a equação vira `a³ + b³ = c³` (`fermatLastTheoremThree`);
* `4 ∣ x`, `4 ∣ y`, `2 ∣ z`: a equação vira `a⁴ + b⁴ = c²` (`not_fermat_42`, descida de Fermat).

Exemplos: `(3, 6, 9)`, `(6, 3, 12)`, `(4, 8, 6)`, `(8, 4, 10)`.

Nessas assinaturas a equação não tem solução positiva, então a conclusão de Beal vale por
vacuidade. São corolários de Fermat, não progresso no caso geral: `OPEN_MATH = true`.
-/

namespace BealPrizeProof

/-- Beal restrito à assinatura `(x, y, z)`. -/
def SignatureCase (x y z : ℕ) : Prop :=
  ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C → A ^ x + B ^ y = C ^ z →
    ∃ p : ℕ, p.Prime ∧ p ∣ A ∧ p ∣ B ∧ p ∣ C

/-- `SignatureCase x y z` é a especialização do enunciado fixado. -/
theorem signatureCase_of_statement (h : BealPrize.Statement) {x y z : ℕ}
    (hx : 2 < x) (hy : 2 < y) (hz : 2 < z) : SignatureCase x y z :=
  fun A B C hA hB hC hE => h A B C x y z hA hB hC hx hy hz hE

/-- Se a equação não tem solução positiva na assinatura, Beal vale nela por vacuidade. -/
theorem signatureCase_of_noSolution {x y z : ℕ}
    (h : ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C → A ^ x + B ^ y ≠ C ^ z) :
    SignatureCase x y z :=
  fun A B C hA hB hC hE => absurd hE (h A B C hA hB hC)

/-- Assinaturas com `3 ∣ x`, `3 ∣ y`, `3 ∣ z`. -/
theorem signatureCase_of_three_dvd {x y z : ℕ} (hx : 3 ∣ x) (hy : 3 ∣ y) (hz : 3 ∣ z) :
    SignatureCase x y z := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := hz
  refine signatureCase_of_noSolution fun A B C hA hB hC hE => ?_
  have hE' : (A ^ a) ^ 3 + (B ^ b) ^ 3 = (C ^ c) ^ 3 := by
    simpa only [← pow_mul, mul_comm] using hE
  exact fermatLastTheoremThree (A ^ a) (B ^ b) (C ^ c) (pow_pos hA a).ne' (pow_pos hB b).ne'
    (pow_pos hC c).ne' hE'

/-- Assinaturas com `4 ∣ x`, `4 ∣ y`, `2 ∣ z`. -/
theorem signatureCase_of_four_four_two {x y z : ℕ} (hx : 4 ∣ x) (hy : 4 ∣ y) (hz : 2 ∣ z) :
    SignatureCase x y z := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := hz
  refine signatureCase_of_noSolution fun A B C hA hB hC hE => ?_
  have hE' : ((A ^ a : ℕ) : ℤ) ^ 4 + ((B ^ b : ℕ) : ℤ) ^ 4 = ((C ^ c : ℕ) : ℤ) ^ 2 := by
    have : (A ^ a) ^ 4 + (B ^ b) ^ 4 = (C ^ c) ^ 2 := by
      simpa only [← pow_mul, mul_comm] using hE
    exact_mod_cast this
  exact not_fermat_42 (by exact_mod_cast (pow_pos hA a).ne') (by exact_mod_cast (pow_pos hB b).ne')
    hE'

/-- Exemplo com expoentes distintos: `(3, 6, 9)`. -/
example : SignatureCase 3 6 9 :=
  signatureCase_of_three_dvd (by norm_num) (by norm_num) (by norm_num)

/-- Exemplo com expoentes distintos: `(4, 8, 6)`. -/
example : SignatureCase 4 8 6 :=
  signatureCase_of_four_four_two (by norm_num) (by norm_num) (by norm_num)

end BealPrizeProof
