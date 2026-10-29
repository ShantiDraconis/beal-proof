import BealPrizeProof.Diagonal
import BealPrizeProof.Reduction
import BealPrizeProof.Signatures

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
