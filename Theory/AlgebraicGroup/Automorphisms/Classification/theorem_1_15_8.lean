module

public import Theory.AlgebraicGroup.Automorphisms.Classification.theorem_1_15_7

/-!
This module isolates `theorem_1_15_8` from `Theory.AlgebraicGroup.Automorphisms.Classification`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_15_8
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (hK : IsSimpleAlgebraicGroup K) (hT : IsMaximalTorus T) :
    {σ : Aut K | σ ∈ AutOneSet K ∧ ∀ t, t ∈ T →
      σ * innerConjugationMap K t = innerConjugationMap K t * σ} =
      innerConjugationMap K '' (T : Set (Variety.Point K)) := by
  apply Set.Subset.antisymm
  · intro σ hσ
    sorry
  · exact maximalTorus_innerConjugations_mem_autOneCentralizer hT

public def HasGroupRootClassification
    {K : Variety k} [AlgebraicGroup K]
    (classification : RootClassification) : Prop :=
  ∃ T : ClosedSubgroup K, ∃ D : RootGroupData K T,
    IsMaximalTorus T ∧ D.IsRealization ∧
      ∃ (ι R M N : Type u) (hι : Finite ι) (hR : Field R)
        (hChar : CharZero R) (hM : AddCommGroup M) (hMR : Module R M)
        (hN : AddCommGroup N) (hNR : Module R N),
        let _ := hι
        let _ := hR
        let _ := hChar
        let _ := hM
        let _ := hMR
        let _ := hN
        let _ := hNR
        ∃ (P : RootPairing ι R M N)
          (hRoot : P.IsRootSystem)
          (hCryst : P.IsCrystallographic)
          (hRed : P.IsReduced),
          let _ := hRoot
          let _ := hCryst
          let _ := hRed
          ∃ eRoot : D.Root ≃ ι,
            (∀ α β, (D.pairing α β : R) = P.pairing (eRoot α) (eRoot β)) ∧
              ∃ b : P.Base, ∃ eBase : b.support ≃ Fin classification.rank,
                (∀ i j,
                  b.cartanMatrixIn ℤ i j =
                    dynkinCartanEntry classification (eBase i) (eBase j)) ∧
                  ∃ eSimple : D.simple ≃ b.support,
                    (∀ α, eRoot α.1 = (eSimple α).1)

end Theory.AlgebraicGroup
