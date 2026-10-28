module

public import Theory.AlgebraicGroup.Solvable.MaximalTorusConjugacy
public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteGeneration
public import Theory.AlgebraicGroup.Borel.StandardPositiveSystemClassification.Defs
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Finite torus-invariant representatives for unipotent components

Let a subtorus `T` normalize a closed unipotent subgroup `X`, which need not
be connected. Every component of `X` contains a point centralizing `T`.
Consequently there is a finite, pointwise fixed set of representatives for
`X / X°`, with the literal ambient factorization `x = y * f`, `y ∈ X°`.

Connectedness of `T` puts its commutators with each point of `X` in `X°`.
Thus `T X°` is a connected solvable closed subgroup containing both `T` and
`x T x⁻¹`. Both are maximal tori there, and solvable torus conjugacy gives a
conjugator in `X°` after removing its torus factor. The remaining point of
`X` normalizes `T`; its commutators belong to both `T` and `X`, whose
intersection is trivial. Finiteness of the genuine component quotient then
supplies finitely many fixed representatives.

This gives the finite-invariant-set input used in the disconnected case of
Borel, *Linear Algebraic Groups*, Chapter IV, §14.4, Proposition (2)(a).
The conjugacy input is Chapter III, Theorem 10.6(4). Unlike the source's
root-coordinate construction, this argument needs only unipotence and torus
invariance. The final application uses the intersection of the two actual
unipotent radicals of Borels associated with positive systems.
-/

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.ComponentTransversal
open scoped Pointwise
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

omit [IsAlgClosed k] in
private lemma carrier_connected (H : ClosedSubgroup G)
    (h : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace h
  let : ConnectedSpace (Variety.Point H.carrierVariety) := e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

omit [IsAlgClosed k] in
private lemma set_connected (H : ClosedSubgroup G) (h : Variety.IsConnected H.carrierVariety) :
    _root_.IsConnected (H : Set (Variety.Point G)) := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace (Variety.Point H.carrierVariety) := connectedSpace_iff_univ.mpr h
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    e.connectedSpace_iff.mp inferInstance
  exact isConnected_iff_connectedSpace.mpr inferInstance

private lemma unipotent_of_le (V U : ClosedSubgroup G) (hle : V ≤ U)
    (hu : IsUnipotentAlgebraicGroup U.carrierVariety) :
    IsUnipotentAlgebraicGroup V.carrierVariety := by
  intro v
  let x := V.inclusion.onPoints v
  have hxV : x ∈ V.toSubgroup := (V.pointEquiv v).property
  have hxU : x ∈ U.toSubgroup := hle hxV
  let u := U.pointEquiv.symm ⟨x, hxU⟩
  have ha := morphism_preserves_unipotentElement U.inclusion u (hu u)
  have hv := closedSubgroup_unipotent_of_ambient V hxV ha
  exact hv

omit [IsAlgClosed k] in
private lemma invariant_normalizer (T X : ClosedSubgroup G) (h : IsClosedSubgroupInvariant T X) :
    T.toSubgroup ≤ Subgroup.normalizer (X.toSubgroup : Set (Variety.Point G)) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    change t * x * t⁻¹ ∈ X
    simpa only [inv_inv] using h t⁻¹ (T.toSubgroup.inv_mem ht) x hx
  · intro hx
    change x ∈ X
    simpa [mul_assoc] using h t ht _ hx

private lemma normalizer_identityComponent (X : ClosedSubgroup G) :
    Subgroup.normalizer (X.toSubgroup : Set (Variety.Point G)) ≤
      Subgroup.normalizer (X.identityComponentAmbient.toSubgroup : Set (Variety.Point G)) := by
  have step (g : Variety.Point G)
      (hg : g ∈ Subgroup.normalizer (X.toSubgroup : Set (Variety.Point G))) :
      X.identityComponentAmbient.conjugate g ≤ X.identityComponentAmbient := by
    apply connected_closedSubgroup_le_identityComponentAmbient
    · exact set_connected _ ((algebraicGroupIso_isConnected_iff
        (X.identityComponentAmbient.conjugateIso g)).mp
          (carrier_connected _ X.identityComponentAmbient_isConnected))
    · intro x hx
      have hi := X.identityComponentAmbient_le
        ((X.identityComponentAmbient.mem_conjugate_iff g x).mp hx)
      have hh := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mp hi
      change x ∈ X.toSubgroup
      simpa [mul_assoc] using hh
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    apply step g hg
    apply (ClosedSubgroup.mem_conjugate_iff _ _ _).mpr
    simpa [mul_assoc] using hx
  · intro hx
    have hh := step g⁻¹ ((Subgroup.normalizer _).inv_mem hg)
    apply hh
    apply (ClosedSubgroup.mem_conjugate_iff _ _ _).mpr
    simpa [mul_assoc] using hx

private lemma connected_map_mem_component (X : ClosedSubgroup G) {V : Variety k}
    (hV : Variety.IsConnected V) (f : Variety.Point V → Variety.Point G)
    (hc : Continuous f) (hX : ∀ v, f v ∈ X) (v₀ : Variety.Point V) (h₀ : f v₀ = 1) :
    ∀ v, f v ∈ X.identityComponentAmbient := by
  let e := Variety.closedSubvarietyPointHomeomorph X.isZariskiClosed
  let f' : Variety.Point V → Variety.Point X.carrierVariety :=
    fun v => e.symm ⟨f v, hX v⟩
  have hc' : Continuous f' := e.symm.continuous.comp (hc.subtype_mk hX)
  have hconn : _root_.IsConnected (Set.range f') := by
    simpa only [Set.image_univ] using hV.image f' hc'.continuousOn
  have hf (v) : X.inclusion.onPoints (f' v) = f v := rfl
  have h1 : f' v₀ = 1 := by
    apply X.inclusion_injective
    rw [hf, map_one, h₀]
  intro v
  apply (X.mem_identityComponentAmbient_iff _).mpr
  refine ⟨f' v, ?_, hf v⟩
  exact hconn.subset_connectedComponent (h1 ▸ Set.mem_range_self v₀)
    (Set.mem_range_self v)

private lemma torus_commutator_mem_component (T X : ClosedSubgroup G) (hT : IsSubtorus T)
    (hTX : IsClosedSubgroupInvariant T X) (x : Variety.Point G) (hx : x ∈ X)
    (t : Variety.Point G) (ht : t ∈ T) :
    t⁻¹ * x * t * x⁻¹ ∈ X.identityComponentAmbient := by
  let f : Variety.Point T.carrierVariety → Variety.Point G :=
    fun s => (T.includePoint s)⁻¹ * x * T.includePoint s * x⁻¹
  have hc : Continuous f := by
    have hi : Continuous (fun s : Variety.Point T.carrierVariety =>
        (T.includePoint s)⁻¹ * x * T.includePoint s) := by
      change Continuous (fun s => (T.inclusion.toVariety.toFun s)⁻¹ * x * T.inclusion.toVariety.toFun s)
      simpa only [Function.comp_def, inverseConjugateMorphism_apply] using
        ((inverseConjugateMorphism G x).continuous.comp T.inclusion.toVariety.continuous)
    exact (Homeomorph.mulRight x⁻¹).continuous.comp
      hi
  have hmem : ∀ s, f s ∈ X := by
    intro s
    exact X.toSubgroup.mul_mem (hTX _ (T.pointEquiv s).property x hx)
      (X.toSubgroup.inv_mem hx)
  have hf := connected_map_mem_component X hT.isConnected f hc hmem 1 (by
    change (T.inclusion.onPoints 1)⁻¹ * x * T.inclusion.onPoints 1 * x⁻¹ = 1
    simp)
  exact hf (T.pointEquiv.symm ⟨t, ht⟩)


private lemma exists_connected_solvable_product (T U : ClosedSubgroup G)
    (hT : IsSubtorus T) (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hUc : _root_.IsConnected (U : Set (Variety.Point G)))
    (hn : T.toSubgroup ≤ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G))) :
    ∃ P : ClosedSubgroup G, P.toSubgroup = T.toSubgroup ⊔ U.toSubgroup ∧
      Variety.IsConnected P.carrierVariety ∧ Group.IsSolvable (Variety.Point P.carrierVariety) := by
  let H : Bool → ClosedSubgroup G := fun b => if b then T else U
  have hc : ∀ b, _root_.IsConnected (H b : Set (Variety.Point G)) := by
    intro b
    cases b
    · exact hUc
    · exact set_connected T hT.isConnected
  have heq : Subgroup.closure (⋃ b, (H b : Set (Variety.Point G))) =
      T.toSubgroup ⊔ U.toSubgroup := by
    have hset : (⋃ b, (H b : Set (Variety.Point G))) =
        (T.toSubgroup : Set (Variety.Point G)) ∪ U.toSubgroup := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨b, hb⟩
        cases b
        · exact Or.inr hb
        · exact Or.inl hb
      · rintro (ht | hu)
        · exact ⟨true, ht⟩
        · exact ⟨false, hu⟩
    rw [hset, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]

  have hclosed := closure_iUnion_connected_closedSubgroup_isZariskiClosed H hc
  rw [heq] at hclosed
  let P : ClosedSubgroup G := ClosedSubgroup.ofSubgroup _ hclosed
  have hpc : Variety.IsConnected P.carrierVariety := by
    apply carrier_connected
    change _root_.IsConnected ((T.toSubgroup ⊔ U.toSubgroup : Subgroup (Variety.Point G)) : Set (Variety.Point G))
    rw [← heq]
    exact closure_iUnion_connected_closedSubgroup_isConnected H hc
  let : Group.IsSolvable (Variety.Point U.carrierVariety) :=
    isSolvable_of_isUnipotentAlgebraicGroup hU
  let eu := Equiv.mulEquiv U.pointEquiv
  let : Group.IsSolvable U.toSubgroup :=
    Group.isSolvable_of_surjective (f := eu.toMonoidHom) eu.surjective
  let : Group.IsSolvable (Variety.Point T.carrierVariety) :=
    Group.isSolvable_of_comm (isMulCommutative_iff.mp hT.isMulCommutative)
  let et := Equiv.mulEquiv T.pointEquiv
  let : Group.IsSolvable T.toSubgroup :=
    Group.isSolvable_of_surjective (f := et.toMonoidHom) et.surjective
  have hs : Group.IsSolvable (T.toSubgroup ⊔ U.toSubgroup : Subgroup _) := by
    rw [sup_comm]
    exact Group.isSolvable_sup_of_normalizes U.toSubgroup T.toSubgroup hn
  let : Group.IsSolvable P.toSubgroup := hs
  let ep := Equiv.mulEquiv P.pointEquiv
  exact ⟨P, rfl, hpc, Group.isSolvable_of_isSolvable_injective (f := ep.toMonoidHom) ep.injective⟩

private def inside (H P : ClosedSubgroup G) : ClosedSubgroup P.carrierVariety :=
  P.inclusion.closedSubgroupPreimage H

omit [IsAlgClosed k] in
private lemma mem_inside (H P : ClosedSubgroup G) (x : Variety.Point P.carrierVariety) :
    x ∈ inside H P ↔ P.inclusion.onPoints x ∈ H := Iff.rfl

private lemma inside_eq_image (H P : ClosedSubgroup G) (hle : H ≤ P) :
    inside H P = (H.inclusion.codRestrictClosedSubgroup P
      (fun x => hle (H.pointEquiv x).property)).imageClosedSubgroup := by
  apply SetLike.coe_injective
  ext x
  change (P.inclusion.onPoints x ∈ H) ↔ ∃ y, _ = x
  constructor
  · intro hx
    refine ⟨H.pointEquiv.symm ⟨P.inclusion.onPoints x, hx⟩, ?_⟩
    apply P.inclusion_injective
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    rfl
  · rintro ⟨y, rfl⟩
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact (H.pointEquiv y).property

private lemma inside_torus (T P : ClosedSubgroup G) (hle : T ≤ P) (hT : IsSubtorus T) :
    IsSubtorus (inside T P) := by
  rw [inside_eq_image T P hle]
  exact morphism_image_isTorus _ hT

local instance (U P : ClosedSubgroup G) : AlgebraicGroup (inside U P).carrierVariety :=
  (inside U P).carrierAlgebraicGroup

private lemma inside_unipotent (U P : ClosedSubgroup G) (hle : U ≤ P)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    IsUnipotentAlgebraicGroup (inside U P).carrierVariety := by
  change @IsUnipotentAlgebraicGroup k _ (inside U P).carrierVariety
    (ClosedSubgroup.carrierAlgebraicGroup (inside U P))
  rw [inside_eq_image U P hle]
  let f := U.inclusion.codRestrictClosedSubgroup P
    (fun x => hle (U.pointEquiv x).property)
  let : AlgebraicGroup f.imageClosedSubgroup.carrierVariety :=
    f.imageClosedSubgroup.carrierAlgebraicGroup
  have hm (x) : f.onPoints x ∈ f.imageClosedSubgroup := ⟨x, rfl⟩
  exact hU.of_surjective (f.codRestrictClosedSubgroup f.imageClosedSubgroup hm)
    (f.codRestrictImageClosedSubgroup_surjective hm)

omit [IsAlgClosed k] in
private lemma inside_factorization (T U P : ClosedSubgroup G) (hTP : T ≤ P) (hUP : U ≤ P)
    (hfactor : ∀ x, x ∈ P → ∃ t, t ∈ T ∧ ∃ u, u ∈ U ∧ x = t * u) :
    ∀ x : Variety.Point P.carrierVariety, ∃ t u,
      t ∈ (inside T P).toSubgroup ∧ u ∈ (inside U P).toSubgroup ∧ x = t * u := by
  intro x
  obtain ⟨t, ht, u, hu, he⟩ := hfactor _ (P.pointEquiv x).property
  let t' := P.pointEquiv.symm ⟨t, hTP ht⟩
  let u' := P.pointEquiv.symm ⟨u, hUP hu⟩
  refine ⟨t', u', ht, hu, ?_⟩
  apply P.inclusion_injective
  exact he

private lemma conjugate_into_by_unipotent (T S U P : ClosedSubgroup G)
    (hT : IsSubtorus T) (hS : IsSubtorus S)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hPc : Variety.IsConnected P.carrierVariety)
    (hPs : Group.IsSolvable (Variety.Point P.carrierVariety))
    (hTP : T ≤ P) (hSP : S ≤ P) (hUP : U ≤ P)
    (hTU : ∀ x, x ∈ P → ∃ t, t ∈ T ∧ ∃ u, u ∈ U ∧ x = t * u)
    (hSU : ∀ x, x ∈ P → ∃ s, s ∈ S ∧ ∃ u, u ∈ U ∧ x = s * u)
    (hUT : ∀ x, x ∈ P → ∃ u, u ∈ U ∧ ∃ t, t ∈ T ∧ x = u * t) :
    ∃ u, u ∈ U ∧ ∀ s, s ∈ S → u⁻¹ * s * u ∈ T := by
  let TI := inside T P
  let SI := inside S P
  let UI := inside U P
  have hTI : IsSubtorus TI := inside_torus T P hTP hT
  have hSI : IsSubtorus SI := inside_torus S P hSP hS
  have hUI : IsUnipotentAlgebraicGroup UI.carrierVariety := inside_unipotent U P hUP hU
  have hTM : IsMaximalTorus TI :=
    IsTorusComplement.isMaximalTorus_of_unipotent
      ⟨hTI, inside_factorization T U P hTP hUP hTU,
        subtorus_inf_unipotent_eq_bot TI UI hTI hUI⟩ hUI
  have hSM : IsMaximalTorus SI :=
    IsTorusComplement.isMaximalTorus_of_unipotent
      ⟨hSI, inside_factorization S U P hSP hUP hSU,
        subtorus_inf_unipotent_eq_bot SI UI hSI hUI⟩ hUI
  obtain ⟨p, hp⟩ := maximalTori_conjugate_of_solvable_connected hPs hPc hTM hSM
  obtain ⟨u, hu, t, ht, he⟩ := hUT (P.inclusion.onPoints p) (P.pointEquiv p).property
  refine ⟨u, hu, ?_⟩
  intro s hs
  let s' := P.pointEquiv.symm ⟨s, hSP hs⟩
  have hsi : s' ∈ SI := hs
  rw [hp, ClosedSubgroup.mem_conjugate_iff] at hsi
  have hi : (P.inclusion.onPoints p)⁻¹ * s * P.inclusion.onPoints p ∈ T := hsi
  rw [he] at hi
  have hh := T.toSubgroup.mul_mem (T.toSubgroup.mul_mem ht hi) (T.toSubgroup.inv_mem ht)
  change u⁻¹ * s * u ∈ T.toSubgroup
  simpa [mul_assoc] using hh

private lemma component_centralizer_factorization (T X : ClosedSubgroup G) (hT : IsSubtorus T)
    (hTX : IsClosedSubgroupInvariant T X) (hX : IsUnipotentAlgebraicGroup X.carrierVariety) :
    ∀ x, x ∈ X → ∃ y, y ∈ X.identityComponentAmbient ∧
      ∃ f, f ∈ X ∧ (∀ t, t ∈ T → t⁻¹ * f * t = f) ∧ x = y * f := by
  let U := X.identityComponentAmbient
  have hUX : U ≤ X := X.identityComponentAmbient_le
  have hU : IsUnipotentAlgebraicGroup U.carrierVariety := unipotent_of_le U X hUX hX
  have hTn : T.toSubgroup ≤ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)) :=
    (invariant_normalizer T X hTX).trans (normalizer_identityComponent X)
  obtain ⟨P, hP, hPc, hPs⟩ := exists_connected_solvable_product T U hT hU
    X.identityComponentAmbient_isConnected hTn
  have hTP : T ≤ P := by change T.toSubgroup ≤ P.toSubgroup; rw [hP]; exact le_sup_left
  have hUP : U ≤ P := by change U.toSubgroup ≤ P.toSubgroup; rw [hP]; exact le_sup_right
  have hTU : ∀ z, z ∈ P → ∃ t, t ∈ T ∧ ∃ u, u ∈ U ∧ z = t * u := by
    intro z hz
    change z ∈ P.toSubgroup at hz
    rw [hP] at hz
    have hm := (Subgroup.coe_mul_of_left_le_normalizer_right T.toSubgroup U.toSubgroup hTn)
    have hz' : z ∈ (T.toSubgroup : Set (Variety.Point G)) * U.toSubgroup := by
      rw [← hm]; exact hz
    obtain ⟨t, ht, u, hu, he⟩ := Set.mem_mul.mp hz'
    exact ⟨t, ht, u, hu, he.symm⟩
  have hUT : ∀ z, z ∈ P → ∃ u, u ∈ U ∧ ∃ t, t ∈ T ∧ z = u * t := by
    intro z hz
    obtain ⟨t, ht, u, hu, rfl⟩ := hTU z hz
    refine ⟨t * u * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTn ht) u).mp hu, t, ht, ?_⟩
    group
  intro x hx
  let S := T.conjugate x
  have hS : IsSubtorus S := by
    obtain ⟨n, ⟨e⟩⟩ := hT
    exact ⟨n, ⟨(T.conjugateIso x).comp e⟩⟩
  have hxn : x ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)) :=
    normalizer_identityComponent X (X.toSubgroup.le_normalizer hx)
  have hSP : S ≤ P := by
    intro s hs
    have ht : x⁻¹ * s * x ∈ T.toSubgroup := (T.mem_conjugate_iff x s).mp hs
    have hc := torus_commutator_mem_component T X hT hTX x hx _ ht
    have hh := P.toSubgroup.mul_mem (hTP ht) (hUP hc)
    change s ∈ P.toSubgroup
    have he : (x⁻¹ * s * x) * ((x⁻¹ * s * x)⁻¹ * x * (x⁻¹ * s * x) * x⁻¹) = s := by group
    rwa [he] at hh
  have hSU : ∀ z, z ∈ P → ∃ s, s ∈ S ∧ ∃ u, u ∈ U ∧ z = s * u := by
    intro z hz
    obtain ⟨t, ht, u, hu, rfl⟩ := hTU z hz
    have hc := torus_commutator_mem_component T X hT hTX x⁻¹
      (X.toSubgroup.inv_mem hx) t ht
    have hc' := (Subgroup.mem_normalizer_iff.mp hxn (t⁻¹ * x⁻¹ * t * (x⁻¹)⁻¹)).mp hc
    have hm : x * t⁻¹ * x⁻¹ * t ∈ U.toSubgroup := by simpa [mul_assoc] using hc'
    refine ⟨x * t * x⁻¹, ?_, (x * t⁻¹ * x⁻¹ * t) * u, U.toSubgroup.mul_mem hm hu, ?_⟩
    · apply (T.mem_conjugate_iff x _).mpr
      have ht' : t ∈ T.toSubgroup := ht
      simpa [mul_assoc] using ht'
    · group
  obtain ⟨u, hu, hconj⟩ := conjugate_into_by_unipotent T S U P hT hS hU
    hPc hPs hTP hSP hUP hTU hSU hUT
  let f := u⁻¹ * x
  have hf : f ∈ X := X.toSubgroup.mul_mem (X.toSubgroup.inv_mem (hUX hu)) hx
  refine ⟨u, hu, f, hf, ?_, by dsimp [f]; group⟩
  intro t ht
  have hs : x * t * x⁻¹ ∈ S := by
    apply (T.mem_conjugate_iff x _).mpr
    have ht' : t ∈ T.toSubgroup := ht
    simpa [mul_assoc] using ht'
  have hft : f * t * f⁻¹ ∈ T := by
    have hh := hconj _ hs
    change f * t * f⁻¹ ∈ T
    convert hh using 1
    dsimp [f]
    group
  have hcT : t⁻¹ * f * t * f⁻¹ ∈ T.toSubgroup := by
    simpa only [mul_assoc] using T.toSubgroup.mul_mem (T.toSubgroup.inv_mem ht) hft
  have hcX : t⁻¹ * f * t * f⁻¹ ∈ X.toSubgroup :=
    X.toSubgroup.mul_mem (hTX t ht f hf) (X.toSubgroup.inv_mem hf)
  have hc1 : t⁻¹ * f * t * f⁻¹ = 1 := by
    have hm : t⁻¹ * f * t * f⁻¹ ∈ T.toSubgroup ⊓ X.toSubgroup := ⟨hcT, hcX⟩
    rw [subtorus_inf_unipotent_eq_bot T X hT hX] at hm
    exact Subgroup.mem_bot.mp hm
  exact mul_right_cancel (hc1.trans (mul_inv_cancel f).symm)

private lemma finite_transversal_of_component_factorization (T X : ClosedSubgroup G)
    (hfactor : ∀ x, x ∈ X → ∃ y, y ∈ X.identityComponentAmbient ∧
      ∃ f, f ∈ X ∧ (∀ t, t ∈ T → t⁻¹ * f * t = f) ∧ x = y * f) :
    ∃ F : Set (Variety.Point G), F.Finite ∧ F ⊆ X ∧
      (∀ t, t ∈ T → ∀ f, f ∈ F → t⁻¹ * f * t = f) ∧
      (∀ x, x ∈ X → ∃ y, y ∈ X.identityComponentAmbient ∧ ∃ f, f ∈ F ∧ x = y * f) := by
  classical
  let I := AlgebraicGroup.identityComponentSubgroup X.carrierVariety
  let : I.Normal := by
    simpa [I, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      AlgebraicGroup.identityComponentClosedSubgroup_isNormal X.carrierVariety
  let Q := Variety.Point X.carrierVariety ⧸ I
  let : Finite Q := finite_quotient_identityComponentSubgroup X.carrierVariety
  have hh (q : Q) := hfactor (X.inclusion.onPoints q.out) (X.pointEquiv q.out).property
  choose y hy f hf hfix heq using hh
  refine ⟨Set.range f, Set.finite_range f, ?_, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact hf q
  · rintro t ht _ ⟨q, rfl⟩
    exact hfix q t ht
  · intro x hx
    let x' := X.pointEquiv.symm ⟨x, hx⟩
    let q : Q := QuotientGroup.mk x'
    have hq : (x' : Q) = QuotientGroup.mk q.out := (Quotient.out_eq q).symm
    have hd : x' * q.out⁻¹ ∈ I := by
      simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hq
    have hd' : x * (X.inclusion.onPoints q.out)⁻¹ ∈ X.identityComponentAmbient := by
      apply (X.mem_identityComponentAmbient_iff _).mpr
      exact ⟨x' * q.out⁻¹, hd, by rw [map_mul, map_inv]; rfl⟩
    refine ⟨x * (X.inclusion.onPoints q.out)⁻¹ * y q,
      X.identityComponentAmbient.toSubgroup.mul_mem hd' (hy q),
      f q, Set.mem_range_self q, ?_⟩
    rw [heq q]
    group

end Theory.AlgebraicGroup.BorelIntersectionGeometry.ComponentTransversal

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- Every component of a torus-invariant unipotent subgroup contains a point
centralizing the torus: `X = X° C_X(T)` at the level of ambient points. -/
public theorem torusInvariant_unipotent_component_factorization
    (T X : ClosedSubgroup G) (hT : IsSubtorus T)
    (hTX : IsClosedSubgroupInvariant T X)
    (hX : IsUnipotentAlgebraicGroup X.carrierVariety) :
    ∀ x, x ∈ X → ∃ y, y ∈ X.identityComponentAmbient ∧
      ∃ f, f ∈ X ∧ (∀ t, t ∈ T → t⁻¹ * f * t = f) ∧ x = y * f :=
  ComponentTransversal.component_centralizer_factorization T X hT hTX hX

/-- A finite set meeting every component of `X`, fixed pointwise by `T`.
No connectedness assumption on `X` is needed. -/
public theorem exists_finite_torusFixed_component_transversal
    (T X : ClosedSubgroup G) (hT : IsSubtorus T)
    (hTX : IsClosedSubgroupInvariant T X)
    (hX : IsUnipotentAlgebraicGroup X.carrierVariety) :
    ∃ F : Set (Variety.Point G), F.Finite ∧ F ⊆ X ∧
      (∀ t, t ∈ T → ∀ f, f ∈ F → t⁻¹ * f * t = f) ∧
      (∀ x, x ∈ X → ∃ y, y ∈ X.identityComponentAmbient ∧
        ∃ f, f ∈ F ∧ x = y * f) :=
  ComponentTransversal.finite_transversal_of_component_factorization T X
    (torusInvariant_unipotent_component_factorization T X hT hTX hX)

/-- The finite invariant transversal used by the disconnected-subgroup step
of Borel IV, §14.4(2)(a), with inverse conjugation as in the invariant-subgroup API. -/
public theorem exists_finite_torusInvariant_component_transversal
    (T X : ClosedSubgroup G) (hT : IsSubtorus T)
    (hTX : IsClosedSubgroupInvariant T X)
    (hX : IsUnipotentAlgebraicGroup X.carrierVariety) :
    ∃ F : Set (Variety.Point G), F.Finite ∧ F ⊆ X ∧
      (∀ t, t ∈ T → ∀ f, f ∈ F → t⁻¹ * f * t ∈ F) ∧
      (∀ x, x ∈ X → ∃ y, y ∈ X.identityComponentAmbient ∧
        ∃ f, f ∈ F ∧ x = y * f) := by
  obtain ⟨F, hF, hFX, hfix, hfactor⟩ :=
    exists_finite_torusFixed_component_transversal T X hT hTX hX
  refine ⟨F, hF, hFX, ?_, hfactor⟩
  intro t ht f hf
  rw [hfix t ht f hf]
  exact hf

/-- The actual intersection of two Borel radicals has a finite torus-invariant
component transversal. Relative normality in the two Borels supplies invariance,
and containment in the first radical supplies unipotence. -/
public theorem radical_inter_exists_finite_torusInvariant_component_transversal
    {T B C : ClosedSubgroup G} (hT : IsSubtorus T)
    (D : RootGroupData G T) {P Q : Set D.Root}
    (hBP : IsBorelOfPositiveSystem D P B) (hCQ : IsBorelOfPositiveSystem D Q C) :
    ∃ F : Set (Variety.Point G), F.Finite ∧
      F ⊆ hBP.unipotent.inter hCQ.unipotent ∧
      (∀ t, t ∈ T → ∀ f, f ∈ F → t⁻¹ * f * t ∈ F) ∧
      (∀ x, x ∈ hBP.unipotent.inter hCQ.unipotent →
        ∃ y, y ∈ (hBP.unipotent.inter hCQ.unipotent).identityComponentAmbient ∧
          ∃ f, f ∈ F ∧ x = y * f) := by
  have hTB : T ≤ B := by
    change T.toSubgroup ≤ B.toSubgroup
    rw [hBP.torus_unipotent_generate]
    exact le_sup_left
  have hTC : T ≤ C := by
    change T.toSubgroup ≤ C.toSubgroup
    rw [hCQ.torus_unipotent_generate]
    exact le_sup_left
  have hTX : IsClosedSubgroupInvariant T
      (hBP.unipotent.inter hCQ.unipotent) := by
    intro t ht x hx
    have htinv : t⁻¹ ∈ T := T.toSubgroup.inv_mem ht
    have hB := hBP.radical.2.2.1 t⁻¹ (hTB htinv) x hx.1
    have hC := hCQ.radical.2.2.1 t⁻¹ (hTC htinv) x hx.2
    change t⁻¹ * x * t ∈ hBP.unipotent ∧ t⁻¹ * x * t ∈ hCQ.unipotent
    simpa only [inv_inv] using And.intro hB hC
  exact exists_finite_torusInvariant_component_transversal T
    (hBP.unipotent.inter hCQ.unipotent) hT hTX
    (ComponentTransversal.unipotent_of_le _ hBP.unipotent
      (fun _ hx => hx.1) hBP.radical.2.1)

end Theory.AlgebraicGroup.BorelIntersectionGeometry
