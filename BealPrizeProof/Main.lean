import BealPrize

/-!
# Conjectura de Beal — prova

O alvo é exatamente o enunciado importado do repositório fixado em `lakefile.toml`:

    theorem main : BealPrize.Statement

Este repositório nunca redefine o enunciado. Enquanto não houver prova completa, este arquivo
não declara `main`: nenhum `sorry`, nenhum `axiom`.

Quando `main` existir, acrescente ao fim deste arquivo (com a saída real do Lean):

    /-- info: 'BealPrizeProof.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
    #guard_msgs in #print axioms BealPrizeProof.main
-/

namespace BealPrizeProof

/-- O enunciado que a prova tem que fechar (igual por definição ao do repositório fixado). -/
abbrev Target : Prop := BealPrize.Statement

end BealPrizeProof
