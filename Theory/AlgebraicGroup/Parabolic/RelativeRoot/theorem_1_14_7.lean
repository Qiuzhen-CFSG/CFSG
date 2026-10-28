module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiberModule_rational
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiberMaxRootHighWeight

/-!
This module isolates `theorem_1_14_7` from `Theory.AlgebraicGroup.Parabolic.RelativeRoot`.
Its elementary fiber-module existence input comes from the preceding source
coordinate and Levi-action construction, and its rationality is supplied by
the concrete regular fiber conjugation morphism. The remaining irreducibility
and highest-weight assertions stay local to this numbered result, preserving
the source order and public API of the GLS3 algebraic-group development.

The maintained fiber representation acts by left conjugation `l * x * l^-1`,
whereas `RootWeightEquation` names the root character using
`t^-1 * x * t`. Consequently the maximal-root high weight in the statement is
the inverse of the root character pulled back to the induced Levi torus. This
is the orientation proved by
`RelativeRootFiberModule.maximalRoot_hasHighWeight_inducedBorel`.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_14_7
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    letI := relativeRootLayerQuotientGroup S
    Nonempty (RelativeRootFiberModule S) ∧
    (∀ M : RelativeRootFiberModule S,
      ∃ e : Module.Basis (Fin (Module.finrank k M.V)) k M.V,
        ∃ f : AlgebraicGroup.Morphism S.L.carrierVariety (glVarietyOf k M.V),
          ∀ l, glPointEquivOf k M.V e (f.onPoints l) = M.representation.action l) ∧
    (∀ M : RelativeRootFiberModule S,
      ¬ IsUSingular S.classification (ringChar k) →
        IsIrreducibleRepresentation M.representation) ∧
    (∃! γ : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root },
      ∀ δ, δ ∈ relativeRootFiberAtHeight
          S.D S.coeff S.J S.height S.root →
        S.D.height δ ≤ S.D.height γ) ∧
    (∀ M : RelativeRootFiberModule S,
      ∀ γ (hγ : γ ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root),
      (∀ δ, δ ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root → S.D.height δ ≤ S.D.height γ) →
      letI : AlgebraicGroup S.L.carrierVariety := S.L.carrierAlgebraicGroup
      let BLevi := S.L.inclusion.closedSubgroupPreimage S.B
      let TLevi := S.L.inclusion.closedSubgroupPreimage S.T
      letI : AlgebraicGroup BLevi.carrierVariety := BLevi.carrierAlgebraicGroup
      letI : AlgebraicGroup TLevi.carrierVariety := TLevi.carrierAlgebraicGroup
      ∃ z : k, z ≠ 0 ∧
        HasHighWeight M.representation BLevi TLevi
          (M.rootVector (⟨γ, hγ⟩, z))
          ((TorusCharacter.pullback (S.L.inclusion.preimageRestriction S.T)
            (S.D.rootWeight γ))⁻¹)) := by sorry

end Theory.AlgebraicGroup
