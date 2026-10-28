module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_layer_levi_action
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.sourceRelativeRootLayer_root_mem
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_chevalley_torus_fiber_bridge
public import Theory.AlgebraicGroup.Representations.Algebraic.RelativeRootQuotientHighWeight

/-!
# Fiber modules use the source Chevalley action

The generator compatibility fields of `RelativeRootFiberModule` determine its
abstract conjugation action uniquely.  This module identifies that action with
the source-Levi action constructed directly from Chevalley conjugation on the
adjacent relative-root quotient.  Transport through `pointEquiv` then gives a
root-vector equivariance formula for `M.representation`.

This is the source-to-representation bridge used by the irreducibility argument:
all action calculations can be made in the concrete source quotient and then
read in `M.V`.  It uses neither numbered relative-root theorem.

The final theorem packages the quotient-first high-weight interface for a
fiber module.  Consumers provide the source action on root labels and
parameters; the linear coordinate contract supplies generator nonvanishing
and parameter homogeneity automatically.
-/

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem RelativeRootFiberModule.action_eq_source_on_generator
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S)
    (l : Variety.Point S.L.carrierVariety)
    (z : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} × k) :
    M.conjugationAction l (relativeRootFiberQuotientGenerator S z) =
      S.sourceFiberConjugationHom l (relativeRootFiberQuotientGenerator S z) := by
  rw [M.conjugationAction_generator]
  rcases M.conjugatedGenerator_value l z with ⟨y, hy, hqy⟩
  rcases S.sourceFiberConjugationHom_generator_value l z with ⟨y', hy', hqy'⟩
  apply Subtype.ext
  rw [hqy, hqy']
  congr 1
  apply Subtype.ext
  exact hy.trans hy'.symm

/-- The action stored by a fiber module is exactly source Chevalley
conjugation restricted to the chosen relative-root fiber. -/
public theorem RelativeRootFiberModule.conjugationAction_eq_sourceFiberConjugationHom
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S) :
    M.conjugationAction = S.sourceFiberConjugationHom := by
  ext l q
  have hq : q.1 ∈ Subgroup.closure (Set.range fun z :
      {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root} × k =>
      QuotientGroup.mk' _ (relativeRootLayerElement S z.1.1 z.1.2 z.2)) := by
    rw [← relativeRootFiberQuotientSubgroup_spec S]
    exact q.2
  have h := Subgroup.closure_induction
    (p := fun x hx => M.conjugationAction l ⟨x, by
        rw [relativeRootFiberQuotientSubgroup_spec S]; exact hx⟩ =
      S.sourceFiberConjugationHom l ⟨x, by
        rw [relativeRootFiberQuotientSubgroup_spec S]; exact hx⟩)
    (fun x hx => by
      rcases hx with ⟨z, rfl⟩
      let qz : relativeRootFiberQuotientSubgroup S := ⟨_, by
        rw [relativeRootFiberQuotientSubgroup_spec S]
        exact Subgroup.subset_closure ⟨z, rfl⟩⟩
      have hqz : qz = relativeRootFiberQuotientGenerator S z := by
        apply Subtype.ext
        exact (relativeRootFiberQuotientGenerator_coe S z).symm
      change M.conjugationAction l qz = S.sourceFiberConjugationHom l qz
      rw [hqz]
      exact M.action_eq_source_on_generator l z)
    (by
      let qone : relativeRootFiberQuotientSubgroup S := ⟨1, by
        rw [relativeRootFiberQuotientSubgroup_spec S]
        exact (Subgroup.closure _).one_mem⟩
      have hone : qone = 1 := by ext; rfl
      change M.conjugationAction l qone = S.sourceFiberConjugationHom l qone
      rw [hone, map_one, map_one]) (by
      intro x y hx hy hx' hy'
      let qx : relativeRootFiberQuotientSubgroup S := ⟨x, by
        rw [relativeRootFiberQuotientSubgroup_spec S]; exact hx⟩
      let qy : relativeRootFiberQuotientSubgroup S := ⟨y, by
        rw [relativeRootFiberQuotientSubgroup_spec S]; exact hy⟩
      have hmul : (⟨x * y, by
          rw [relativeRootFiberQuotientSubgroup_spec S]
          exact (Subgroup.closure _).mul_mem hx hy⟩ :
          relativeRootFiberQuotientSubgroup S) = qx * qy := by ext; rfl
      rw [hmul]
      change M.conjugationAction l (qx * qy) =
        S.sourceFiberConjugationHom l (qx * qy)
      rw [map_mul, map_mul, hx', hy'])
    (by
      intro x hx hx'
      let qx : relativeRootFiberQuotientSubgroup S := ⟨x, by
        rw [relativeRootFiberQuotientSubgroup_spec S]; exact hx⟩
      have hinv : (⟨x⁻¹, by
          rw [relativeRootFiberQuotientSubgroup_spec S]
          exact (Subgroup.closure _).inv_mem hx⟩ :
          relativeRootFiberQuotientSubgroup S) = qx⁻¹ := by ext; rfl
      rw [hinv]
      change M.conjugationAction l qx⁻¹ = S.sourceFiberConjugationHom l qx⁻¹
      rw [map_inv, map_inv, hx']) hq
  exact congrArg Subtype.val h

/-- Transporting source quotient conjugation through `M.pointEquiv` is exactly
the action of `M.representation`.  This packages the pullback/restriction
compatibility needed by consumers without introducing a second action. -/
public theorem RelativeRootFiberModule.representation_agrees_with_sourceFiberConjugation
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S)
    (l : Variety.Point S.L.carrierVariety)
    (q : relativeRootFiberQuotientSubgroup S) :
    M.pointEquiv (S.sourceFiberConjugationHom l q) =
      Multiplicative.ofAdd
        ((M.representation.action l).1
          (Multiplicative.toAdd (M.pointEquiv q))) := by
  rw [← M.conjugationAction_eq_sourceFiberConjugationHom]
  exact M.representation_agrees_with_conjugation l q

/-- The full source coordinate rational representation restricts on a fiber
quotient to the supported coordinates of source Chevalley conjugation. -/
public theorem
    RelativeRootRepresentationSource.sourceCoordinateRepresentation_restricts_to_fiber
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (q : relativeRootFiberQuotientSubgroup S) :
    (((Multiplicative.toAdd
        (relativeRootFiberSupportedCoordinateEquiv S
          (S.sourceFiberConjugationHom l q)) :
            sourceRelativeRootFiberCoordinateSubmodule S) :
              RelativeRootSourceExactIndex S → k)) =
      (S.sourceLayerCoordinateRationalRepresentation.action l).1
        (((Multiplicative.toAdd
          (relativeRootFiberSupportedCoordinateEquiv S q) :
            sourceRelativeRootFiberCoordinateSubmodule S) :
              RelativeRootSourceExactIndex S → k)) := by
  exact S.sourceFiberConjugationHom_coordinate l q

/-- Root vectors are equivariant for the concrete source Chevalley action and
the representation carried by `M`. -/
public theorem RelativeRootFiberModule.representation_action_rootVector
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S)
    (l : Variety.Point S.L.carrierVariety)
    (z : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} × k) :
    (M.representation.action l).1 (M.rootVector z) =
      Multiplicative.toAdd
        (M.pointEquiv (S.sourceFiberConjugationHom l
          (relativeRootFiberQuotientGenerator S z))) := by
  rw [M.rootVector_value]
  have h := M.representation_agrees_with_conjugation l
    (relativeRootFiberQuotientGenerator S z)
  rw [M.conjugationAction_eq_sourceFiberConjugationHom] at h
  exact congrArg Multiplicative.toAdd h |>.symm

/-- The quotient-first root-action criterion specialized to the canonical
linear realization carried by a relative-root fiber module.  Nonvanishing and
parameter homogeneity are consequences of the fiber coordinate equivalence. -/
public theorem RelativeRootFiberModule.rootVector_hasHighWeight_of_quotientRootAction
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S)
    (rootAction : Variety.Point S.L.carrierVariety →
      {γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root} →
      {γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root})
    (rootScalar : Variety.Point S.L.carrierVariety →
      {γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root} → k → k)
    (hRootVector : ∀ l γ z,
      (M.representation.action l).1 (M.rootVector (γ, z)) =
        M.rootVector (rootAction l γ, rootScalar l γ z))
    (B₀ T₀ : ClosedSubgroup S.L.carrierVariety)
    (γ : {δ : S.D.Root // δ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root})
    (z : k) (hz : z ≠ 0) (χ : TorusWeight T₀)
    (hBfixed : ∀ l, l ∈ B₀ → rootAction l γ = γ)
    (hTfixed : ∀ t : Variety.Point T₀.carrierVariety,
      rootAction (T₀.includePoint t) γ = γ)
    (hTscalar : letI := S.L.carrierAlgebraicGroup
      letI := T₀.carrierAlgebraicGroup
      ∀ t : Variety.Point T₀.carrierVariety,
        rootScalar (T₀.includePoint t) γ z = χ.pointCharacter t * z) :
    HasHighWeight M.representation B₀ T₀ (M.rootVector (γ, z)) χ := by
  apply relativeRootFiberGenerator_hasHighWeight_of_quotientRootAction
    S.D S.J S.coeff S.height S.root M.representation
    (fun γ z => M.rootVector (γ, z)) rootAction rootScalar hRootVector
    B₀ T₀ γ z hz χ
  · exact M.rootVector_ne_zero γ hz
  · intro c
    exact M.rootVector_smul γ c z
  · exact hBfixed
  · exact hTfixed
  · exact hTscalar

end Theory.AlgebraicGroup
