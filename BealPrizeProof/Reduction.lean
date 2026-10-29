import BealPrize

/-!
# Beal ⟺ forma coprima

A literatura trata Beal como a afirmação de que a equação `A^x + B^y = C^z` (a "equação de
Fermat generalizada") não tem solução com `A` e `B` coprimos quando `x, y, z > 2`. Este arquivo
prova que essa forma é equivalente ao enunciado fixado `BealPrize.Statement`. Qualquer resultado
da literatura sobre soluções coprimas passa a valer contra o enunciado fixado por este teorema.

É uma redução, não progresso no problema: `OPEN_MATH = true`.
-/

namespace BealPrizeProof

/-- Forma coprima: não existe solução com `A` e `B` coprimos. -/
def CoprimeForm : Prop :=
  ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C → 2 < x → 2 < y → 2 < z →
    Nat.Coprime A B → A ^ x + B ^ y ≠ C ^ z

/-- Se um primo divide `A` e `B` numa solução, ele divide `C`. -/
theorem prime_dvd_C {p A B C x y z : ℕ} (hp : p.Prime) (hx : 0 < x) (hy : 0 < y)
    (hA : p ∣ A) (hB : p ∣ B) (hE : A ^ x + B ^ y = C ^ z) : p ∣ C := by
  have h1 : p ∣ A ^ x := dvd_pow hA hx.ne'
  have h2 : p ∣ B ^ y := dvd_pow hB hy.ne'
  have h3 : p ∣ C ^ z := hE ▸ Nat.dvd_add h1 h2
  exact hp.dvd_of_dvd_pow h3

/-- `BealPrize.Statement ⟺ CoprimeForm`. -/
theorem statement_iff_coprimeForm : BealPrize.Statement ↔ CoprimeForm := by
  constructor
  · intro h A B C x y z hA hB hC hx hy hz hcop hE
    obtain ⟨p, hp, hpA, hpB, -⟩ := h A B C x y z hA hB hC hx hy hz hE
    have : p ∣ Nat.gcd A B := Nat.dvd_gcd hpA hpB
    rw [hcop] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · intro h A B C x y z hA hB hC hx hy hz hE
    by_cases hg : Nat.gcd A B = 1
    · exact absurd hE (h A B C x y z hA hB hC hx hy hz hg)
    · have hp : (Nat.gcd A B).minFac.Prime := Nat.minFac_prime hg
      have hpA : (Nat.gcd A B).minFac ∣ A := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left A B)
      have hpB : (Nat.gcd A B).minFac ∣ B := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right A B)
      exact ⟨_, hp, hpA, hpB,
        prime_dvd_C hp (by omega) (by omega) hpA hpB hE⟩

end BealPrizeProof
