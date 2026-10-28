module

public import Theory.AlgebraicGroup.Solvable.TorusDecomposition
public import Theory.AlgebraicGroup.Unipotent.Radical

/-!
# Solvable subgroup decomposition over a supplied radical

This module gives the supplied-radical form of Borel, *Linear Algebraic
Groups*, Chapter III, Theorem 10.6(4).  If `R` is a connected solvable closed
subgroup of an ambient algebraic group, `T` is an ambient maximal torus lying
in `R`, and `U` is the supplied unipotent radical of `R`, then every point of
`R` factors as a point of `T` times a point of `U`.  Consequently
`R = T ⊔ U`, and the torus--unipotent intersection is trivial.  This is the
form needed to factor the intersection of two Borels containing a common
maximal torus.

The proof regards `T` as a closed subgroup of `R` and proves that it remains
maximal there by mapping any larger internal torus back to the ambient group.
The intrinsic solvable torus decomposition then supplies a unipotent radical
inside `R`.  Its ambient image is unipotent and hence lies in the supplied
radical by maximality, which transfers the intrinsic pointwise factorization.
The final intersection statement uses the independent torus--unipotent
intersection theorem.  In particular, the argument does not use the later
theorems `theorem_1_5_1_d` or `theorem_1_4_3_d`.
-/

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma carrier_isConnected_of_set_isConnected
    {G : Variety k} [AlgebraicGroup G] (R : ClosedSubgroup G)
    (hR : _root_.IsConnected (R : Set (Variety.Point G))) :
    Variety.IsConnected R.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
  let : ConnectedSpace
      {x : Variety.Point G // x ∈ (R : Set (Variety.Point G))} :=
    Subtype.connectedSpace hR
  let : ConnectedSpace (Variety.Point R.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

private noncomputable def subgroupInside
    {G : Variety k} [AlgebraicGroup G]
    (S R : ClosedSubgroup G) (hSR : S ≤ R) :
    ClosedSubgroup R.carrierVariety := by
  let f : AlgebraicGroup.Morphism S.carrierVariety R.carrierVariety :=
    S.inclusion.codRestrictClosedSubgroup R
      (fun x => hSR (S.pointEquiv x).property)
  exact f.imageClosedSubgroup

private theorem mem_subgroupInside_iff
    {G : Variety k} [AlgebraicGroup G]
    (S R : ClosedSubgroup G) (hSR : S ≤ R)
    (x : Variety.Point R.carrierVariety) :
    letI : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
    x ∈ subgroupInside S R hSR ↔ R.includePoint x ∈ S := by
  let _ : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism S.carrierVariety R.carrierVariety :=
    S.inclusion.codRestrictClosedSubgroup R
      (fun y => hSR (S.pointEquiv y).property)
  have hf (y : Variety.Point S.carrierVariety) :
      R.inclusion.onPoints (f.onPoints y) = S.inclusion.onPoints y :=
    S.inclusion.codRestrictClosedSubgroup_inclusion_apply R
      (fun z => hSR (S.pointEquiv z).property) y
  change (∃ y, f.onPoints y = x) ↔ R.includePoint x ∈ S
  constructor
  · rintro ⟨y, rfl⟩
    change R.inclusion.onPoints (f.onPoints y) ∈ S
    rw [hf]
    exact (S.pointEquiv y).property
  · intro hx
    let y : Variety.Point S.carrierVariety :=
      S.pointEquiv.symm ⟨R.includePoint x, hx⟩
    refine ⟨y, R.inclusion_injective ?_⟩
    rw [hf]
    exact congrArg Subtype.val
      (S.pointEquiv.apply_symm_apply ⟨R.includePoint x, hx⟩)

private theorem subgroupInside_isMaximalTorus
    {G : Variety k} [AlgebraicGroup G]
    (T R : ClosedSubgroup G) (hTR : T ≤ R)
    (hT : IsMaximalTorus T) :
    letI : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
    IsMaximalTorus (subgroupInside T R hTR) := by
  let _ : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism T.carrierVariety R.carrierVariety :=
    T.inclusion.codRestrictClosedSubgroup R
      (fun x => hTR (T.pointEquiv x).property)
  let TI : ClosedSubgroup R.carrierVariety := subgroupInside T R hTR
  have hTItorus : IsSubtorus TI := by
    change IsSubtorus f.imageClosedSubgroup
    exact morphism_image_isTorus f hT.1
  refine ⟨hTItorus, ?_⟩
  intro S hS hTIS
  let _ : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  let j : AlgebraicGroup.Morphism S.carrierVariety G :=
    R.inclusion.comp S.inclusion
  let SA : ClosedSubgroup G := j.imageClosedSubgroup
  have hSAtorus : IsSubtorus SA := morphism_image_isTorus j hS
  have hTSA : T ≤ SA := by
    intro x hxT
    have hxR : x ∈ R := hTR hxT
    let xR : Variety.Point R.carrierVariety :=
      R.pointEquiv.symm ⟨x, hxR⟩
    have hxRval : R.includePoint xR = x := by
      exact congrArg Subtype.val
        (R.pointEquiv.apply_symm_apply ⟨x, hxR⟩)
    have hxTI : xR ∈ TI :=
      (mem_subgroupInside_iff T R hTR xR).mpr (by
        rw [hxRval]
        exact hxT)
    have hxS : xR ∈ S := hTIS hxTI
    let xS : Variety.Point S.carrierVariety :=
      S.pointEquiv.symm ⟨xR, hxS⟩
    change x ∈ j.image
    refine ⟨xS, ?_⟩
    change R.inclusion.onPoints (S.inclusion.onPoints xS) = x
    rw [← hxRval]
    exact congrArg R.inclusion.onPoints
      (congrArg Subtype.val (S.pointEquiv.apply_symm_apply ⟨xR, hxS⟩))
  have hSAT : SA = T := hT.2 SA hSAtorus hTSA
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro x hxS
    apply (mem_subgroupInside_iff T R hTR x).mpr
    have hxSA : R.includePoint x ∈ SA := by
      let xS : Variety.Point S.carrierVariety :=
        S.pointEquiv.symm ⟨x, hxS⟩
      change R.inclusion.onPoints x ∈ j.image
      refine ⟨xS, ?_⟩
      change R.inclusion.onPoints (S.inclusion.onPoints xS) =
        R.inclusion.onPoints x
      exact congrArg R.inclusion.onPoints
        (congrArg Subtype.val (S.pointEquiv.apply_symm_apply ⟨x, hxS⟩))
    rw [hSAT] at hxSA
    exact hxSA
  · exact hTIS

/-- A connected solvable subgroup is the pointwise product of a contained
ambient maximal torus and its supplied unipotent radical, and the two factors
have trivial intersection. -/
public theorem maximalTorus_unipotentRadical_decomposition_of_connected_solvable
    {G : Variety k} [AlgebraicGroup G]
    {R U T : ClosedSubgroup G}
    (hRconnected : _root_.IsConnected (R : Set (Variety.Point G)))
    (hRsolvable : Group.IsSolvable (Variety.Point R.carrierVariety))
    (hU : IsUnipotentRadicalOf R U)
    (hT : IsMaximalTorus T) (hTR : T ≤ R) :
    (∀ x : Variety.Point G, x ∈ R.toSubgroup →
      ∃ t u, t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u) ∧
      R.toSubgroup = T.toSubgroup ⊔ U.toSubgroup ∧
      T.toSubgroup ⊓ U.toSubgroup = ⊥ := by
  let _ : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  let TI : ClosedSubgroup R.carrierVariety := subgroupInside T R hTR
  have hTI : IsMaximalTorus TI :=
    subgroupInside_isMaximalTorus T R hTR hT
  have hRcarrierConnected : Variety.IsConnected R.carrierVariety :=
    carrier_isConnected_of_set_isConnected R hRconnected
  obtain ⟨UR, _hURradical, _hURconnected, hURunipotent, hTIUR⟩ :=
    exists_unipotentRadical_complement_of_maximalTorus_solvable_connected
      hRsolvable hRcarrierConnected TI hTI
  let _ : AlgebraicGroup UR.carrierVariety := UR.carrierAlgebraicGroup
  let j : AlgebraicGroup.Morphism UR.carrierVariety G :=
    R.inclusion.comp UR.inclusion
  let UA : ClosedSubgroup G := j.imageClosedSubgroup
  have hUAleR : UA ≤ R := by
    intro x hx
    change x ∈ j.image at hx
    obtain ⟨y, rfl⟩ := hx
    exact (R.pointEquiv (UR.inclusion.onPoints y)).property
  have hUAunipotent : IsUnipotentAlgebraicGroup UA.carrierVariety := by
    let p : AlgebraicGroup.Morphism UR.carrierVariety UA.carrierVariety :=
      j.codRestrictClosedSubgroup UA (fun y => ⟨y, rfl⟩)
    apply hURunipotent.of_surjective p
    exact j.codRestrictImageClosedSubgroup_surjective (fun y => ⟨y, rfl⟩)
  have hUAleU : UA ≤ U :=
    hU.contains_unipotent_closedSubgroup hRconnected hRsolvable
      hUAleR hUAunipotent
  have hfactor : ∀ x : Variety.Point G, x ∈ R.toSubgroup →
      ∃ t u, t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u := by
    intro x hxR
    let xR : Variety.Point R.carrierVariety :=
      R.pointEquiv.symm ⟨x, hxR⟩
    obtain ⟨tR, uR, htR, huR, hmul⟩ := hTIUR.2.1 xR
    let t : Variety.Point G := R.includePoint tR
    let u : Variety.Point G := R.includePoint uR
    have ht : t ∈ T.toSubgroup :=
      (mem_subgroupInside_iff T R hTR tR).mp htR
    have huUA : u ∈ UA.toSubgroup := by
      let uUR : Variety.Point UR.carrierVariety :=
        UR.pointEquiv.symm ⟨uR, huR⟩
      change u ∈ j.image
      refine ⟨uUR, ?_⟩
      change R.inclusion.onPoints (UR.inclusion.onPoints uUR) =
        R.inclusion.onPoints uR
      exact congrArg R.inclusion.onPoints
        (congrArg Subtype.val (UR.pointEquiv.apply_symm_apply ⟨uR, huR⟩))
    refine ⟨t, u, ht, hUAleU huUA, ?_⟩
    have hmulAmbient := congrArg R.inclusion.onPoints hmul
    change x = R.inclusion.onPoints tR * R.inclusion.onPoints uR
    rw [show R.inclusion.onPoints xR = x by
      exact congrArg Subtype.val
        (R.pointEquiv.apply_symm_apply ⟨x, hxR⟩)] at hmulAmbient
    exact hmulAmbient
  refine ⟨hfactor, ?_, ?_⟩
  · apply le_antisymm
    · intro x hxR
      obtain ⟨t, u, ht, hu, rfl⟩ := hfactor x hxR
      exact (T.toSubgroup ⊔ U.toSubgroup).mul_mem
        (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hu)
    · exact sup_le hTR hU.1
  · exact subtorus_inf_unipotent_eq_bot T U hT.1 hU.2.1

end Theory.AlgebraicGroup
