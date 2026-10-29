import BealPrizeProof.Diagonal

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
