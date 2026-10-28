module

public import Theory.AlgebraicGroup.Automorphisms.Classification.theorem_1_15_8

/-!
This module isolates `theorem_1_15_9` from `Theory.AlgebraicGroup.Automorphisms.Classification`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_15_9
    {K H Ka Ha : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    [AlgebraicGroup Ka] [AlgebraicGroup Ha]
    (hK : IsSimpleAlgebraicGroup K) (hH : IsSimpleAlgebraicGroup H)
    (πK : AlgebraicGroup.Morphism K Ka) (πH : AlgebraicGroup.Morphism H Ha)
    (hπK : IsIsogeny πK) (hπH : IsIsogeny πH)
    (hKa : IsAdjointVersion Ka) (hHa : IsAdjointVersion Ha)
    (hAdj : ¬ Nonempty (AlgebraicGroup.Iso Ka Ha))
    (typeK typeH : RootClassification)
    (hTypeK : HasGroupRootClassification (K := Ka) typeK)
    (hTypeH : HasGroupRootClassification (K := Ha) typeH) :
    (∃ φ : AlgebraicGroup.Morphism K H, Function.Surjective φ.onPoints) ↔
      ringChar k = 2 ∧ ∃ m ≥ 3,
        ((typeK.kind = .B ∧ typeH.kind = .C ∧ typeK.rank = m ∧ typeH.rank = m) ∨
         (typeK.kind = .C ∧ typeH.kind = .B ∧ typeK.rank = m ∧ typeH.rank = m)) := by sorry

end Theory.AlgebraicGroup
