import BealPrizeProof.Signatures
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Algebra.GCDMonoid.Nat

/-!
# `A⁶ + B⁶ ≠ C²` (Euler, via FLT(3)) e as assinaturas `(6a, 6b, 2c)`

`sixth_add_sixth_ne_sq_of_coprime`: `A⁶ + B⁶ ≠ C²` para `A, B > 0` coprimos. A prova usa só o
Mathlib:

1. um dos dois é par (`A⁶ + B⁶ ≡ 2 (mód 4)` não é quadrado); digamos `A` ímpar, `B = 2B₁`;
2. `(A³, B³, C)` é uma tripla pitagórica primitiva: `A³ = M² − N²`, `B³ = 2MN`, `M > N > 0`
   coprimos de paridades opostas (`PythagoreanTriple.coprime_classification'`);
3. `M − N` e `M + N` são coprimos com produto `A³`, logo cubos `s³`, `t³`; e `MN = 4B₁³` com o
   fator par igual a `4u³`;
4. se `M = 4u³`, `s³ + t³ = 2M = (2u)³`; se `N = 4u³`, `s³ + (2u)³ = t³` — ambos contradizem
   FLT(3) (`fermatLastTheoremThree`, Mathlib).

**A coprimalidade não é necessária.** `sixth_add_sixth_ne_sq` tira a hipótese: com
`g = mdc(A, B)`, `A = gA'`, `B = gB'`, a equação dá `g⁶ ∣ C²`, logo `g³ ∣ C`, e dividindo por
`g⁶` obtém-se uma solução coprima `A'⁶ + B'⁶ = (C/g³)²`. (O kernel ATK fazia a redução no nível de
Beal, com `mdc(A, B) > 1 ⇒` primo comum que divide `C`; aqui ela é feita na própria equação, o que
dá o resultado mais forte "sem solução positiva alguma".)

Consequência para Beal: `signatureCase_of_six_six_two` (`6 ∣ x`, `6 ∣ y`, `2 ∣ z`), por vacuidade,
porque `A^x + B^y = C^z` vira `(A^a)⁶ + (B^b)⁶ = (C^c)²`.

Origem: portado do ATK kernel, `ATK/DarmonMerelSeis.lean` (`cubo`, `par_cubo`, `seis_impar`,
`dmSq_seis`) e `ATK/BealSeisSeisDois.lean` (`sem_solucao_662`, `beal_662`) — espelho público
`atk-math-core-public/imports/M-Core/atk-kernel`, M-Core commit `390e378`. A redução sem
coprimalidade (`sixth_add_sixth_ne_sq`) é nova neste repositório.
Matemática clássica (Euler); não é progresso no caso geral de Beal: `OPEN_MATH = true`.
-/

namespace BealPrizeProof

/-- Fatores coprimos de um cubo em `ℕ` são cubos. -/
theorem eq_cube_of_coprime_mul_eq_cube {a b c : ℕ} (h : Nat.Coprime a b) (he : a * b = c ^ 3) :
    ∃ d, a = d ^ 3 :=
  exists_eq_pow_of_mul_eq_pow (by rw [Nat.isUnit_iff]; exact h) he

/-- Se `o` é ímpar, coprimo com `e`, e `o·e = 4B³`, então `e = 4u³`. -/
theorem eq_four_mul_cube_of_odd_mul {o e B : ℕ} (ho : Odd o) (hc : Nat.Coprime o e)
    (h : o * e = 4 * B ^ 3) : ∃ u, e = 4 * u ^ 3 := by
  have h2o : Nat.Coprime 2 o := Nat.coprime_two_left.mpr ho
  have h4o : Nat.Coprime 4 o := by
    have := Nat.Coprime.pow_left 2 h2o
    norm_num at this
    exact this
  have h4 : 4 ∣ e := by
    apply h4o.dvd_of_dvd_mul_left
    exact ⟨B ^ 3, h⟩
  obtain ⟨e₂, rfl⟩ := h4
  have h' : e₂ * o = B ^ 3 := by
    have : 4 * (e₂ * o) = 4 * B ^ 3 := by rw [← h]; ring
    omega
  have hc' : Nat.Coprime e₂ o :=
    (Nat.Coprime.coprime_dvd_right (Dvd.intro_left 4 rfl) hc).symm
  obtain ⟨u, hu⟩ := eq_cube_of_coprime_mul_eq_cube hc' h'
  exact ⟨u, by rw [hu]⟩

/-- O caso `A` ímpar de `A⁶ + B⁶ ≠ C²` (`A, B` coprimos). -/
theorem sixth_add_sixth_ne_sq_of_odd {A B C : ℕ} (hA : Odd A) (hB : 0 < B)
    (hAB : Nat.Coprime A B) (h : A ^ 6 + B ^ 6 = C ^ 2) : False := by
  -- `B` é par (mód 4)
  have hBe : Even B := by
    by_contra hBo
    rw [Nat.not_even_iff_odd] at hBo
    have hA4 : A % 4 = 1 ∨ A % 4 = 3 := by obtain ⟨k, rfl⟩ := hA; omega
    have hB4 : B % 4 = 1 ∨ B % 4 = 3 := by obtain ⟨k, rfl⟩ := hBo; omega
    have hC4 : C % 4 = 0 ∨ C % 4 = 1 ∨ C % 4 = 2 ∨ C % 4 = 3 := by omega
    have hm : (A ^ 6 + B ^ 6) % 4 = C ^ 2 % 4 := by rw [h]
    rw [Nat.add_mod, Nat.pow_mod A, Nat.pow_mod B, Nat.pow_mod C] at hm
    rcases hA4 with h1 | h1 <;> rcases hB4 with h2 | h2 <;>
      rcases hC4 with h3 | h3 | h3 | h3 <;> rw [h1, h2, h3] at hm <;> norm_num at hm
  obtain ⟨B₁, hB₁⟩ := hBe
  -- tripla pitagórica primitiva `(A³, B³, C)`
  have hC : 0 < C := by
    rcases Nat.eq_zero_or_pos C with rfl | hC
    · have : 0 < A ^ 6 + B ^ 6 := by positivity
      rw [h] at this
      norm_num at this
    · exact hC
  have hpt : PythagoreanTriple ((A : ℤ) ^ 3) ((B : ℤ) ^ 3) (C : ℤ) := by
    unfold PythagoreanTriple
    have : ((A ^ 6 + B ^ 6 : ℕ) : ℤ) = ((C ^ 2 : ℕ) : ℤ) := by rw [h]
    push_cast at this
    linear_combination this
  have hgcd : Int.gcd ((A : ℤ) ^ 3) ((B : ℤ) ^ 3) = 1 := by
    have : ((A : ℤ) ^ 3) = ((A ^ 3 : ℕ) : ℤ) := by push_cast; rfl
    have h2 : ((B : ℤ) ^ 3) = ((B ^ 3 : ℕ) : ℤ) := by push_cast; rfl
    rw [this, h2, Int.gcd_natCast_natCast]
    exact Nat.Coprime.pow 3 3 hAB
  have hpar : (A : ℤ) ^ 3 % 2 = 1 := by
    have : Odd ((A : ℤ) ^ 3) := by exact_mod_cast hA.pow
    exact Int.odd_iff.mp this
  obtain ⟨m, n, hx, hy, -, hmn, hpar2, hm0⟩ :=
    PythagoreanTriple.coprime_classification' hpt hgcd hpar (by exact_mod_cast hC)
  -- `m > n > 0`
  have hBpos : (0 : ℤ) < (B : ℤ) ^ 3 := by positivity
  have hApos : (0 : ℤ) < (A : ℤ) ^ 3 := by
    have : 0 < A := hA.pos
    positivity
  have hmpos : 0 < m := by
    rcases hm0.lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0] at hy; simp at hy; linarith
  have hnpos : 0 < n := by
    by_contra hn
    have hn' : n ≤ 0 := not_lt.mp hn
    have : 2 * m * n ≤ 0 := by nlinarith
    linarith
  have hnm : n < m := by
    by_contra hc
    have hc' : m ≤ n := not_lt.mp hc
    have : m ^ 2 - n ^ 2 ≤ 0 := by nlinarith
    linarith
  obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hnpos.le
  have hNM : N < M := by exact_mod_cast hnm
  have hN0 : 0 < N := by exact_mod_cast hnpos
  -- de volta a `ℕ`
  have hx' : (M - N) * (M + N) = A ^ 3 := by
    have : (((M - N) * (M + N) : ℕ) : ℤ) = ((A ^ 3 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hNM.le]
      linear_combination -hx
    exact_mod_cast this
  have hy' : 2 * M * N = B ^ 3 := by
    have : ((2 * M * N : ℕ) : ℤ) = ((B ^ 3 : ℕ) : ℤ) := by
      push_cast
      linear_combination -hy
    exact_mod_cast this
  have hcop : Nat.Coprime M N := by
    rw [Int.gcd_natCast_natCast] at hmn
    exact hmn
  have hparN : (M % 2 = 0 ∧ N % 2 = 1) ∨ (M % 2 = 1 ∧ N % 2 = 0) := by omega
  -- `M − N` e `M + N` são coprimos, logo cubos
  have hcop2 : Nat.Coprime (M - N) (M + N) := by
    have h1 : Nat.gcd (M - N) (M + N) ∣ 2 * M := by
      have := Nat.dvd_add (Nat.gcd_dvd_left (M - N) (M + N)) (Nat.gcd_dvd_right (M - N) (M + N))
      rwa [show M - N + (M + N) = 2 * M by omega] at this
    have h2 : Nat.gcd (M - N) (M + N) ∣ 2 * N := by
      have := Nat.dvd_sub (Nat.gcd_dvd_right (M - N) (M + N)) (Nat.gcd_dvd_left (M - N) (M + N))
      rwa [show M + N - (M - N) = 2 * N by omega] at this
    have h3 := Nat.dvd_gcd h1 h2
    rw [Nat.gcd_mul_left, hcop, mul_one] at h3
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h4 | h4
    · exact h4
    · exfalso
      have h5 := Nat.gcd_dvd_right (M - N) (M + N)
      rw [h4] at h5
      omega
  obtain ⟨s, hs⟩ := eq_cube_of_coprime_mul_eq_cube hcop2 hx'
  obtain ⟨t, ht⟩ := eq_cube_of_coprime_mul_eq_cube hcop2.symm (by rw [mul_comm]; exact hx')
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    omega
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
    omega
  have hMN : M * N = 4 * B₁ ^ 3 := by
    have : 2 * (M * N) = 2 * (4 * B₁ ^ 3) := by
      rw [← mul_assoc, hy', hB₁]; ring
    omega
  rcases hparN with ⟨hM2, hN2⟩ | ⟨hM2, hN2⟩
  · -- `M = 4u³`: `s³ + t³ = 2M = (2u)³`
    obtain ⟨u, hu⟩ := eq_four_mul_cube_of_odd_mul (Nat.odd_iff.mpr hN2)
      hcop.symm (by rw [mul_comm]; exact hMN)
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
      omega
    apply fermatLastTheoremThree s t (2 * u) hs0 ht0 (by positivity)
    rw [← hs, ← ht]
    have : M - N + (M + N) = 2 * M := by omega
    rw [this, hu]
    ring
  · -- `N = 4u³`: `s³ + (2u)³ = t³`
    obtain ⟨u, hu⟩ := eq_four_mul_cube_of_odd_mul (Nat.odd_iff.mpr hM2) hcop hMN
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu
      omega
    apply fermatLastTheoremThree s (2 * u) t hs0 (by positivity) ht0
    rw [← hs, ← ht]
    have : M + N = M - N + 2 * N := by omega
    rw [this, hu]
    ring

/-- **Euler**: `A⁶ + B⁶ ≠ C²` para `A, B > 0` coprimos (via FLT(3) do Mathlib e a classificação
das triplas pitagóricas). É `dmSq_seis` do ATK kernel. -/
theorem sixth_add_sixth_ne_sq_of_coprime {A B C : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hAB : Nat.Coprime A B) : A ^ 6 + B ^ 6 ≠ C ^ 2 := by
  intro h
  rcases Nat.even_or_odd A with hAe | hAo
  · rcases Nat.even_or_odd B with hBe | hBo
    · have h2 : 2 ∣ Nat.gcd A B := Nat.dvd_gcd (even_iff_two_dvd.mp hAe) (even_iff_two_dvd.mp hBe)
      rw [hAB] at h2
      omega
    · exact sixth_add_sixth_ne_sq_of_odd hBo hA hAB.symm (by rw [add_comm]; exact h)
  · exact sixth_add_sixth_ne_sq_of_odd hAo hB hAB h

/-- `A⁶ + B⁶ ≠ C²` para **quaisquer** `A, B > 0` (sem coprimalidade): divide-se por
`mdc(A, B)⁶`, usando `mdc(A, B)³ ∣ C`. -/
theorem sixth_add_sixth_ne_sq {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) : A ^ 6 + B ^ 6 ≠ C ^ 2 := by
  intro h
  obtain ⟨g, A', B', hg, hcop, rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_left B hA)
  have hA' : 0 < A' := Nat.pos_of_mul_pos_right hA
  have hB' : 0 < B' := Nat.pos_of_mul_pos_right hB
  have hdiv : (g ^ 3) ^ 2 ∣ C ^ 2 :=
    ⟨A' ^ 6 + B' ^ 6, by rw [← h]; ring⟩
  obtain ⟨C', rfl⟩ := (Nat.pow_dvd_pow_iff two_ne_zero).mp hdiv
  have hg6 : 0 < g ^ 6 := pow_pos hg 6
  have h' : g ^ 6 * (A' ^ 6 + B' ^ 6) = g ^ 6 * C' ^ 2 := by
    rw [show g ^ 6 * (A' ^ 6 + B' ^ 6) = (A' * g) ^ 6 + (B' * g) ^ 6 by ring, h]
    ring
  exact sixth_add_sixth_ne_sq_of_coprime hA' hB' hcop (Nat.eq_of_mul_eq_mul_left hg6 h')

/-- Sem solução positiva quando `6 ∣ x`, `6 ∣ y`, `2 ∣ z` (sem coprimalidade, sem `0 < x, y`). -/
theorem noSolution_six_six_two {A B C x y z : ℕ} (hx : 6 ∣ x) (hy : 6 ∣ y) (hz : 2 ∣ z)
    (hA : 0 < A) (hB : 0 < B) : A ^ x + B ^ y ≠ C ^ z := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := hz
  intro heq
  refine sixth_add_sixth_ne_sq (C := C ^ c) (pow_pos hA a) (pow_pos hB b) ?_
  simpa only [← pow_mul, mul_comm] using heq

/-- Beal nas assinaturas com `6 ∣ x`, `6 ∣ y`, `2 ∣ z`. -/
theorem signatureCase_of_six_six_two {x y z : ℕ} (hx : 6 ∣ x) (hy : 6 ∣ y) (hz : 2 ∣ z) :
    SignatureCase x y z :=
  signatureCase_of_noSolution fun _ _ _ hA hB _ => noSolution_six_six_two hx hy hz hA hB

/-- `(6, 6, 2)`: `A⁶ + B⁶ = C²` não tem solução positiva. Fora da faixa de Beal (`z = 2`). -/
example : SignatureCase 6 6 2 :=
  signatureCase_of_six_six_two (by norm_num) (by norm_num) (by norm_num)

/-- `(12, 6, 4)`. (Também coberto por `(4a, 2b, 4c)`, `RightTriangle.lean`.) -/
example : SignatureCase 12 6 4 :=
  signatureCase_of_six_six_two (by norm_num) (by norm_num) (by norm_num)

/-- `(6, 6, 4)`, `(6, 12, 10)`, `(18, 6, 14)`: dentro da faixa de Beal, `mdc = 2`, e fora de
`3 ∣ x, y, z`, `(4a, 4b, 2c)`, `(4a, 2b, 4c)` e `(2a, 4b, 4c)`. -/
example : SignatureCase 6 6 4 ∧ SignatureCase 6 12 10 ∧ SignatureCase 18 6 14 :=
  ⟨signatureCase_of_six_six_two (by norm_num) (by norm_num) (by norm_num),
    signatureCase_of_six_six_two (by norm_num) (by norm_num) (by norm_num),
    signatureCase_of_six_six_two (by norm_num) (by norm_num) (by norm_num)⟩

end BealPrizeProof
