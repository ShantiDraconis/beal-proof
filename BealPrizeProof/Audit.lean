import BealPrizeProof.Diagonal
import BealPrizeProof.Reduction
import BealPrizeProof.Signatures
import BealPrizeProof.RightTriangle
import BealPrizeProof.SixSixTwo
import BealPrizeProof.Pairwise

/-!
# Auditoria de axiomas

Cada `#guard_msgs` fixa a saída de `#print axioms`. Se aparecer qualquer axioma diferente
(inclusive `sorryAx`), a compilação falha. `Classical.choice` nos casos 3 e 4 vem das provas de
Fermat do Mathlib (corpos ciclotômicos, descida infinita sobre ℤ[ω] etc.).
-/

/-- info: 'BealPrizeProof.DiagonalCase' depends on axioms: [propext] -/
#guard_msgs in #print axioms BealPrizeProof.DiagonalCase

/-- info: 'BealPrizeProof.diagonalCase_of_statement' depends on axioms: [propext] -/
#guard_msgs in #print axioms BealPrizeProof.diagonalCase_of_statement

/-- info: 'BealPrizeProof.diagonalCase_of_fermat' depends on axioms: [propext] -/
#guard_msgs in #print axioms BealPrizeProof.diagonalCase_of_fermat

/-- info: 'BealPrizeProof.diagonalCase_of_three_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.diagonalCase_of_three_dvd

/-- info: 'BealPrizeProof.diagonalCase_of_four_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.diagonalCase_of_four_dvd

/-- info: 'BealPrizeProof.CoprimeForm' depends on axioms: [propext] -/
#guard_msgs in #print axioms BealPrizeProof.CoprimeForm

/-- info: 'BealPrizeProof.prime_dvd_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.prime_dvd_C

/-- info: 'BealPrizeProof.statement_iff_coprimeForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.statement_iff_coprimeForm

/-- info: 'BealPrizeProof.SignatureCase' depends on axioms: [propext] -/
#guard_msgs in #print axioms BealPrizeProof.SignatureCase

/-- info: 'BealPrizeProof.signatureCase_of_statement' depends on axioms: [propext] -/
#guard_msgs in #print axioms BealPrizeProof.signatureCase_of_statement

/-- info: 'BealPrizeProof.signatureCase_of_noSolution' depends on axioms: [propext] -/
#guard_msgs in #print axioms BealPrizeProof.signatureCase_of_noSolution

/-- info: 'BealPrizeProof.signatureCase_of_three_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.signatureCase_of_three_dvd

/-- info: 'BealPrizeProof.signatureCase_of_four_four_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.signatureCase_of_four_four_two

/-! ## `RightTriangle.lean` -/

/-- info: 'BealPrizeProof.FermatM42' depends on axioms: [propext] -/
#guard_msgs in #print axioms BealPrizeProof.FermatM42

/-- info: 'BealPrizeProof.FermatM42.a_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.FermatM42.a_ne_zero

/-- info: 'BealPrizeProof.FermatM42.neg_a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.FermatM42.neg_a

/-- info: 'BealPrizeProof.FermatM42.of_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.FermatM42.of_mul

/-- info: 'BealPrizeProof.FermatM42.Minimal' depends on axioms: [propext] -/
#guard_msgs in #print axioms BealPrizeProof.FermatM42.Minimal

/-- info: 'BealPrizeProof.FermatM42.exists_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.FermatM42.exists_minimal

/-- info: 'BealPrizeProof.FermatM42.coprime_of_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.FermatM42.coprime_of_minimal

/-- info: 'BealPrizeProof.FermatM42.exists_pos_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.FermatM42.exists_pos_minimal

/-- info: 'BealPrizeProof.isCoprime_sq_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.isCoprime_sq_sub

/-- info: 'BealPrizeProof.fermatM42_descent_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.fermatM42_descent_odd

/-- info: 'BealPrizeProof.fermatM42_descent_even_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.fermatM42_descent_even_core

/-- info: 'BealPrizeProof.fermatM42_descent_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.fermatM42_descent_even

/-- info: 'BealPrizeProof.FermatM42.not_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.FermatM42.not_minimal

/-- info: 'BealPrizeProof.not_fermat_4m4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.not_fermat_4m4

/-- info: 'BealPrizeProof.not_fourth_add_sq_eq_fourth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.not_fourth_add_sq_eq_fourth

/-- info: 'BealPrizeProof.noSolution_four_two_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.noSolution_four_two_four

/-- info: 'BealPrizeProof.noSolution_two_four_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.noSolution_two_four_four

/-- info: 'BealPrizeProof.signatureCase_of_four_two_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.signatureCase_of_four_two_four

/-- info: 'BealPrizeProof.signatureCase_of_two_four_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.signatureCase_of_two_four_four

/-! ## `SixSixTwo.lean` -/

/-- info: 'BealPrizeProof.eq_cube_of_coprime_mul_eq_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.eq_cube_of_coprime_mul_eq_cube

/-- info: 'BealPrizeProof.eq_four_mul_cube_of_odd_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.eq_four_mul_cube_of_odd_mul

/-- info: 'BealPrizeProof.sixth_add_sixth_ne_sq_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.sixth_add_sixth_ne_sq_of_odd

/-- info: 'BealPrizeProof.sixth_add_sixth_ne_sq_of_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.sixth_add_sixth_ne_sq_of_coprime

/-- info: 'BealPrizeProof.sixth_add_sixth_ne_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.sixth_add_sixth_ne_sq

/-- info: 'BealPrizeProof.noSolution_six_six_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.noSolution_six_six_two

/-- info: 'BealPrizeProof.signatureCase_of_six_six_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.signatureCase_of_six_six_two

/-! ## `Pairwise.lean` -/

/-- info: 'BealPrizeProof.PairwiseForm' depends on axioms: [propext] -/
#guard_msgs in #print axioms BealPrizeProof.PairwiseForm

/-- info: 'BealPrizeProof.GcdOneForm' depends on axioms: [propext] -/
#guard_msgs in #print axioms BealPrizeProof.GcdOneForm

/-- info: 'BealPrizeProof.prime_dvd_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.prime_dvd_B

/-- info: 'BealPrizeProof.prime_dvd_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.prime_dvd_A

/-- info: 'BealPrizeProof.coprime_AC_of_coprime_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.coprime_AC_of_coprime_AB

/-- info: 'BealPrizeProof.coprime_BC_of_coprime_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.coprime_BC_of_coprime_AB

/-- info: 'BealPrizeProof.coprimeForm_iff_pairwiseForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.coprimeForm_iff_pairwiseForm

/-- info: 'BealPrizeProof.statement_iff_pairwiseForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.statement_iff_pairwiseForm

/-- info: 'BealPrizeProof.statement_iff_gcdOneForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BealPrizeProof.statement_iff_gcdOneForm
