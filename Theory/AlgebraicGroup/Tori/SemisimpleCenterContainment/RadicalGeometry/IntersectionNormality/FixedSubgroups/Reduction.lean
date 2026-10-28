module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.FixedSubgroups.TangentLinear
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.Basic
public import Theory.AlgebraicGroup.Tori.Character.ConnectedKernel
public import Theory.AlgebraicGroup.RootSubgroups.Tangent

/-!
The weight-space reductions for Borel III, 9.5 and IV, 13.16.

The two external-action tangent inputs remain explicit here: decomposition of
the embedded tangent into torus weight spaces, and lifting a fixed embedded
tangent through the fixed subgroup. Nontrivial weights are fixed by their
connected character kernels, which are codimension-one subtori. The trivial
weight is assigned to the full torus, including for a rank-zero acting torus.

These are conditional reductions, not unconditional source-theorem wrappers.
The fixed-subgroup connectedness theorem is in `FixedSubgroups.Connected`.
-/

universe u

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality

open Bor1

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The actual codimension-one closed subtori of `T`, in the ambient group. -/
public abbrev CodimensionOneSubtorus
    {G : Variety k} [AlgebraicGroup G] (T : ClosedSubgroup G) :=
  {Q : ClosedSubgroup G // IsSubtorus Q ∧ Q ≤ T ∧
    Variety.dimension Q.carrierVariety + 1 = Variety.dimension T.carrierVariety}

/-- Decomposition into the ambient representation's weights, for the embedded
tangent of a subgroup. This is the precise linear input used below. -/
@[expose]
public def HasExternalTangentWeightDecomposition
    {G : Variety k} [AlgebraicGroup G] (H T : ClosedSubgroup G) : Prop :=
  (⨆ chi : TorusWeight T,
    closedSubgroupTangent H ⊓ weightSpace (identityTangentRepresentation G) T chi) =
      closedSubgroupTangent H

/-- The fixed-to-geometric-tangent inclusion for subtori of `T` acting on `H`.
It is a tangent-lifting assertion, with no dimension or generation conclusion. -/
@[expose]
public def HasExternalFixedTangentLifting
    {G : Variety k} [AlgebraicGroup G] (H T : ClosedSubgroup G) : Prop :=
  ∀ Q : ClosedSubgroup G, IsSubtorus Q → Q ≤ T →
    ∀ D : IdentityPointDerivation G, D ∈ closedSubgroupTangent H →
      (∀ q : Variety.Point Q.carrierVariety,
        identityTangentConjugationLinearMap G (Q.includePoint q) D = D) →
      D ∈ closedSubgroupTangent (H.pointwiseCentralizer Q)

/-- Weight decomposition and fixed-tangent lifting span `L(H)` by the fixed
tangents of `T` and its codimension-one subtori. -/
public theorem externalTorusFixed_tangent_span
    {G : Variety k} [AlgebraicGroup G] (H T : ClosedSubgroup G)
    (hT : IsSubtorus T)
    (hweights : HasExternalTangentWeightDecomposition H T)
    (hfixed : HasExternalFixedTangentLifting H T) :
    closedSubgroupTangent H ≤
      closedSubgroupTangent (H.pointwiseCentralizer T) ⊔
        ⨆ Q : CodimensionOneSubtorus T,
          closedSubgroupTangent (H.pointwiseCentralizer Q.1) := by
  rw [← hweights]
  apply iSup_le
  intro chi D hD
  by_cases hchi : chi = 1
  · apply Submodule.mem_sup_left
    apply hfixed T hT (fun _ hx => hx) D hD.1
    intro t
    have hw := hD.2 t
    have hone : (1 : TorusWeight T).pointCharacter t = 1 := rfl
    rw [hchi, hone, one_smul] at hw
    apply Derivation.ext
    intro f
    rw [identityTangentConjugationLinearMap_apply]
    have hf := congrArg (fun E : IdentityPointDerivation G => E f) hw
    rw [Theory.AlgebraicGroup.identityTangentRepresentation_action_apply] at hf
    exact hf
  · let Q := chi.ambientConnectedKernel T
    have hpack := chi.connectedKernel_codimension_one T hT hchi
    let q : CodimensionOneSubtorus T :=
      ⟨Q, hpack.ambientConnectedKernel_isSubtorus,
        hpack.ambientConnectedKernel_le, hpack.ambientConnectedKernel_dimension_add_one⟩
    apply Submodule.mem_sup_right
    apply (le_iSup (fun R : CodimensionOneSubtorus T =>
      closedSubgroupTangent (H.pointwiseCentralizer R.1)) q)
    apply hfixed Q hpack.ambientConnectedKernel_isSubtorus
      hpack.ambientConnectedKernel_le D hD.1
    intro s
    obtain ⟨t, ht, heq⟩ :=
      (hpack.mem_ambientConnectedKernel_iff (Q.includePoint s)).mp (Q.pointEquiv s).property
    have hker : chi.onPoints t = 1 :=
      chi.kernelClosedSubgroup.identityComponentAmbient_le ht
    have hpoint : chi.pointCharacter t = 1 := by
      change (dPointEquiv 1 (chi.onPoints t) 0 : k) = 1
      rw [hker, dPointEquiv_one]
      rfl
    have hw := hD.2 t
    have heq' : T.includePoint t = Q.includePoint s := heq
    rw [heq', hpoint, one_smul] at hw
    apply Derivation.ext
    intro f
    rw [identityTangentConjugationLinearMap_apply]
    have hf := congrArg (fun E : IdentityPointDerivation G => E f) hw
    rw [Theory.AlgebraicGroup.identityTangentRepresentation_action_apply] at hf
    exact hf

/-- The dimension step of 13.16 from the two explicit tangent inputs. There is
no normality hypothesis on `U`, nor any quotient-group construction. -/
public theorem externalTorusFixed_dimension_le_of_tangent_inputs
    {G : Variety k} [AlgebraicGroup G] (H U T S : ClosedSubgroup G)
    (hT : IsSubtorus T)
    (hweights : HasExternalTangentWeightDecomposition H T)
    (hfixed : HasExternalFixedTangentLifting H T)
    (hTU : H.pointwiseCentralizer T ≤ U)
    (hother : ∀ Q : CodimensionOneSubtorus T,
      Q.1 ≠ S → H.pointwiseCentralizer Q.1 ≤ U)
    (hlocal : Variety.dimension (H.pointwiseCentralizer S).carrierVariety ≤
      Variety.dimension ((H.pointwiseCentralizer S).inter U).carrierVariety + 1) :
    Variety.dimension H.carrierVariety ≤ Variety.dimension U.carrierVariety + 1 := by
  apply dimension_le_add_of_tangent_le_sup H U (H.pointwiseCentralizer S) 1 _ hlocal
  apply (externalTorusFixed_tangent_span H T hT hweights hfixed).trans
  apply sup_le
  · exact (closedSubgroupTangent_mono hTU).trans le_sup_left
  · apply iSup_le
    intro Q
    by_cases hQS : Q.1 = S
    · rw [hQS]
      exact le_sup_right
    · exact (closedSubgroupTangent_mono (hother Q hQS)).trans le_sup_left

/-- Actual abstract subgroup generation from the two explicit tangent inputs.
Identity components of the fixed subgroups first give closed generation; the
full fixed subgroups then give the same abstract subgroup. -/
public theorem externalTorusFixed_generation_of_tangent_inputs
    {G : Variety k} [AlgebraicGroup G] (H T : ClosedSubgroup G)
    (hHc : _root_.IsConnected (H : Set (Variety.Point G)))
    (hT : IsSubtorus T)
    (hweights : HasExternalTangentWeightDecomposition H T)
    (hfixed : HasExternalFixedTangentLifting H T) :
    Subgroup.closure
      ((H.pointwiseCentralizer T : Set (Variety.Point G)) ∪
        ⋃ Q : CodimensionOneSubtorus T,
          (H.pointwiseCentralizer Q.1 : Set (Variety.Point G))) = H.toSubgroup := by
  let F : Option (CodimensionOneSubtorus T) → ClosedSubgroup G := fun q =>
    match q with
    | none => H.pointwiseCentralizer T
    | some Q => H.pointwiseCentralizer Q.1
  let C := fun q => (F q).identityComponentAmbient
  have hFH (q) : F q ≤ H := by
    cases q <;> exact fun _ hx => hx.1
  have hCH (q) : C q ≤ H :=
    fun _ hx => hFH q ((F q).identityComponentAmbient_le hx)
  have hspan : closedSubgroupTangent H ≤ ⨆ q, closedSubgroupTangent (C q) := by
    apply (externalTorusFixed_tangent_span H T hT hweights hfixed).trans
    apply sup_le
    · have h := le_iSup (fun q => closedSubgroupTangent (C q)) none
      simpa only [C, F, closedSubgroupTangent_identityComponent] using h
    · apply iSup_le
      intro Q
      have h := le_iSup (fun q => closedSubgroupTangent (C q)) (some Q)
      simpa only [C, F, closedSubgroupTangent_identityComponent] using h
  have hgen := subgroupClosure_eq_of_tangent_span H C hHc
    (fun q => (F q).identityComponentAmbient_isConnected) hCH hspan
  apply le_antisymm
  · apply (Subgroup.closure_le H.toSubgroup).mpr
    intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · obtain ⟨Q, hx⟩ := Set.mem_iUnion.mp hx
      exact hx.1
  · rw [← hgen]
    apply Subgroup.closure_mono
    intro x hx
    obtain ⟨q, hx⟩ := Set.mem_iUnion.mp hx
    have hxF := (F q).identityComponentAmbient_le hx
    cases q with
    | none => exact Or.inl hxF
    | some Q => exact Or.inr (Set.mem_iUnion.mpr ⟨Q, hxF⟩)

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
