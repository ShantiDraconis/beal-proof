import BealPrizeProof.Reduction

/-!
# Beal ⟺ nenhuma solução dois a dois coprima

Lei de propagação: numa solução de `A^x + B^y = C^z` (`x, y, z > 0`), **um primo que divide
dois dos três termos divide o terceiro**. Logo, se `A` e `B` são coprimos, também `A, C` e `B, C`
são coprimos, e uma solução ou é dois a dois coprima ou já satisfaz a conclusão de Beal.

* `statement_iff_pairwiseForm`: `BealPrize.Statement ↔ PairwiseForm`;
* `statement_iff_gcdOneForm`: `BealPrize.Statement ↔ GcdOneForm` (`mdc(A, B, C) = 1`).

Junto com `statement_iff_coprimeForm` (`Reduction.lean`), as três formas "primitivas" usadas na
literatura ficam equivalentes ao enunciado fixado. São reduções, não progresso no problema:
`OPEN_MATH = true`.

Origem: portado do ATK kernel, `ATK/BealReduction.lean` (`primo_ac_divide_b`,
`primo_bc_divide_a`, `coprime_ac_de_ab`, `coprime_bc_de_ab`, `primitive_iff_pairwise`,
`beal_iff_pairwise`, `beal_iff_gcdOne`) — espelho público
`atk-math-core-public/imports/M-Core/atk-kernel`, M-Core commit `390e378`. O ATK prova
`beal_iff_gcdOne` passando por `GCDLowerBound`; aqui a prova é direta.
-/

namespace BealPrizeProof

/-- Forma dois a dois coprima: não existe solução com `A, B, C` dois a dois coprimos. -/
def PairwiseForm : Prop :=
  ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C → 2 < x → 2 < y → 2 < z →
    Nat.Coprime A B → Nat.Coprime A C → Nat.Coprime B C → A ^ x + B ^ y ≠ C ^ z

/-- Forma `mdc(A, B, C) = 1`. -/
def GcdOneForm : Prop :=
  ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C → 2 < x → 2 < y → 2 < z →
    Nat.gcd A (Nat.gcd B C) = 1 → A ^ x + B ^ y ≠ C ^ z

/-- Se um primo divide `A` e `C` numa solução, ele divide `B`. -/
theorem prime_dvd_B {p A B C x y z : ℕ} (hp : p.Prime) (hx : 0 < x) (hz : 0 < z)
    (hA : p ∣ A) (hC : p ∣ C) (hE : A ^ x + B ^ y = C ^ z) : p ∣ B := by
  have h1 : p ∣ A ^ x := dvd_pow hA hx.ne'
  have h3 : p ∣ C ^ z := dvd_pow hC hz.ne'
  rw [← hE] at h3
  exact hp.dvd_of_dvd_pow ((Nat.dvd_add_right h1).mp h3)

/-- Se um primo divide `B` e `C` numa solução, ele divide `A`. -/
theorem prime_dvd_A {p A B C x y z : ℕ} (hp : p.Prime) (hy : 0 < y) (hz : 0 < z)
    (hB : p ∣ B) (hC : p ∣ C) (hE : A ^ x + B ^ y = C ^ z) : p ∣ A := by
  have h2 : p ∣ B ^ y := dvd_pow hB hy.ne'
  have h3 : p ∣ C ^ z := dvd_pow hC hz.ne'
  rw [← hE] at h3
  exact hp.dvd_of_dvd_pow ((Nat.dvd_add_left h2).mp h3)

/-- Numa solução, `A, B` coprimos implica `A, C` coprimos. -/
theorem coprime_AC_of_coprime_AB {A B C x y z : ℕ} (hx : 0 < x) (hz : 0 < z)
    (hE : A ^ x + B ^ y = C ^ z) (hAB : Nat.Coprime A B) : Nat.Coprime A C := by
  by_contra h
  obtain ⟨p, hp, hpA, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpB := prime_dvd_B hp hx hz hpA hpC hE
  exact hp.not_dvd_one (by rw [← hAB.gcd_eq_one]; exact Nat.dvd_gcd hpA hpB)

/-- Numa solução, `A, B` coprimos implica `B, C` coprimos. -/
theorem coprime_BC_of_coprime_AB {A B C x y z : ℕ} (hy : 0 < y) (hz : 0 < z)
    (hE : A ^ x + B ^ y = C ^ z) (hAB : Nat.Coprime A B) : Nat.Coprime B C := by
  by_contra h
  obtain ⟨p, hp, hpB, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpA := prime_dvd_A hp hy hz hpB hpC hE
  exact hp.not_dvd_one (by rw [← hAB.gcd_eq_one]; exact Nat.dvd_gcd hpA hpB)

/-- `CoprimeForm ⟺ PairwiseForm`. -/
theorem coprimeForm_iff_pairwiseForm : CoprimeForm ↔ PairwiseForm := by
  constructor
  · intro h A B C x y z hA hB hC hx hy hz hAB _ _
    exact h A B C x y z hA hB hC hx hy hz hAB
  · intro h A B C x y z hA hB hC hx hy hz hAB hE
    exact h A B C x y z hA hB hC hx hy hz hAB
      (coprime_AC_of_coprime_AB (by omega) (by omega) hE hAB)
      (coprime_BC_of_coprime_AB (by omega) (by omega) hE hAB) hE

/-- **`BealPrize.Statement ⟺ PairwiseForm`** (nenhuma solução dois a dois coprima). -/
theorem statement_iff_pairwiseForm : BealPrize.Statement ↔ PairwiseForm :=
  statement_iff_coprimeForm.trans coprimeForm_iff_pairwiseForm

/-- **`BealPrize.Statement ⟺ GcdOneForm`** (nenhuma solução com `mdc(A, B, C) = 1`). -/
theorem statement_iff_gcdOneForm : BealPrize.Statement ↔ GcdOneForm := by
  constructor
  · intro h A B C x y z hA hB hC hx hy hz hg hE
    obtain ⟨p, hp, hpA, hpB, hpC⟩ := h A B C x y z hA hB hC hx hy hz hE
    have : p ∣ Nat.gcd A (Nat.gcd B C) := Nat.dvd_gcd hpA (Nat.dvd_gcd hpB hpC)
    rw [hg] at this
    exact hp.not_dvd_one this
  · intro h
    refine statement_iff_pairwiseForm.mpr fun A B C x y z hA hB hC hx hy hz hAB _ _ => ?_
    refine h A B C x y z hA hB hC hx hy hz ?_
    exact Nat.eq_one_of_dvd_one (hAB ▸ Nat.gcd_dvd_gcd_of_dvd_right A (Nat.gcd_dvd_left B C))

end BealPrizeProof
