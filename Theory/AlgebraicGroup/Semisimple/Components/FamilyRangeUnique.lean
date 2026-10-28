module

public import Theory.AlgebraicGroup.Semisimple.Components.theorem_1_7_2_d
public import Theory.AlgebraicGroup.Simple.Basic
public import Theory.AlgebraicGroup.ClosedSubgroup.CentralSeries
public import Theory.AlgebraicGroup.Morphism.ClosedImage
public import Theory.AlgebraicGroup.Morphism.CodRestrict

universe u

/-!
Uniqueness of a semisimple component family.

This is the uniqueness argument underlying GLS3, Theorem 1.7.2(e).  Every
component is normal in the ambient point group, and the components in either
family generate that group.  Hence a fixed component has a nontrivial
commutator with some component of the other family.  The Zariski closure of
that mixed commutator is connected and lies in their intersection.  After
restricting its inclusion to either component, its closed image is a connected
normal subgroup.  Simplicity makes both images the whole component, so the two
components coincide.  Applying this in both directions identifies the ranges.

Only the component-family infrastructure preceding the unresolved existence
part of `theorem_1_7_2_d` is used; neither that theorem nor the downstream
`theorem_1_7_2_e` participates in the proof.
-/

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace IsSemisimpleComponentFamily

omit [IsAlgClosed k] in
private theorem ClosedSubgroup.carrierVariety_isConnected
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G)
    (hS : _root_.IsConnected (S : Set (Variety.Point G))) :
    Variety.IsConnected S.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph S.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (S : Set (Variety.Point G))} :=
    Subtype.connectedSpace hS
  let : ConnectedSpace (Variety.Point S.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

omit [IsAlgClosed k] in
private theorem ClosedSubgroup.carrierVariety_set_isConnected
    {G : Variety k} [AlgebraicGroup G] (S : ClosedSubgroup G)
    (hS : Variety.IsConnected S.carrierVariety) :
    _root_.IsConnected (S : Set (Variety.Point G)) := by
  let e := Variety.closedSubvarietyPointHomeomorph S.isZariskiClosed
  let : ConnectedSpace (Variety.Point S.carrierVariety) :=
    connectedSpace_iff_univ.mpr hS
  rw [isConnected_iff_connectedSpace]
  exact e.connectedSpace_iff.mp inferInstance

private lemma eq_of_commutator_ne_bot
    {G : Variety k} [AlgebraicGroup G]
    (A B : ClosedSubgroup G)
    (hA : IsSimpleAlgebraicGroup A.carrierVariety)
    (hB : IsSimpleAlgebraicGroup B.carrierVariety)
    (hAn : A.toSubgroup.Normal) (hBn : B.toSubgroup.Normal)
    (hne : ⁅A.toSubgroup, B.toSubgroup⁆ ≠ ⊥) : A = B := by
  let D : ClosedSubgroup G :=
    subgroupZariskiClosure G ⁅A.toSubgroup, B.toSubgroup⁆
  have hDn : D.toSubgroup.Normal :=
    subgroupZariskiClosure_isNormal G _ (inferInstance :
      (⁅A.toSubgroup, B.toSubgroup⁆ : Subgroup (Variety.Point G)).Normal)
  have hDA : D ≤ A := by
    intro x hx
    change x ∈ closure ((⁅A.toSubgroup, B.toSubgroup⁆ :
      Subgroup (Variety.Point G)) : Set (Variety.Point G)) at hx
    exact closure_minimal (Subgroup.commutator_le_left A.toSubgroup B.toSubgroup)
      (Variety.isClosed_iff_isZariskiClosed.mpr A.isZariskiClosed) hx
  have hDB : D ≤ B := by
    intro x hx
    change x ∈ closure ((⁅A.toSubgroup, B.toSubgroup⁆ :
      Subgroup (Variety.Point G)) : Set (Variety.Point G)) at hx
    exact closure_minimal (Subgroup.commutator_le_right A.toSubgroup B.toSubgroup)
      (Variety.isClosed_iff_isZariskiClosed.mpr B.isZariskiClosed) hx
  have hDconn : _root_.IsConnected (D : Set (Variety.Point G)) :=
    subgroupZariskiClosure_commutator_closedSubgroups_isConnected A B
      (ClosedSubgroup.carrierVariety_set_isConnected A hA.1)
  let fA := D.inclusion.codRestrictClosedSubgroup A
    (fun x => hDA (D.pointEquiv x).property)
  let IA := fA.imageClosedSubgroup
  have hIAn : IA.toSubgroup.Normal := by
    refine ⟨?_⟩
    intro x hx y
    change x ∈ fA.image at hx
    rcases hx with ⟨z, rfl⟩
    let yg : Variety.Point G := A.inclusion.onPoints y
    let zg : Variety.Point G := D.inclusion.onPoints z
    have hzD : zg ∈ D := (D.pointEquiv z).property
    have hcD : yg * zg * yg⁻¹ ∈ D := hDn.conj_mem zg hzD yg
    let w : Variety.Point D.carrierVariety := D.pointEquiv.symm ⟨yg * zg * yg⁻¹, hcD⟩
    refine ⟨w, A.inclusion_injective ?_⟩
    simp only [map_mul, map_inv]
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    change D.inclusion.onPoints w = yg * zg * yg⁻¹
    change (D.pointEquiv w).val = yg * zg * yg⁻¹
    rw [D.pointEquiv.apply_symm_apply]
  have hIAconn : _root_.IsConnected (IA : Set (Variety.Point A.carrierVariety)) :=
    fA.imageClosedSubgroup_isConnected
      (ClosedSubgroup.carrierVariety_isConnected D hDconn)
  have hIAbot : IA.toSubgroup ≠ ⊥ := by
    intro hbot
    apply hne
    apply le_antisymm
    · intro x hx
      have hxD : x ∈ D := subset_closure hx
      let z : Variety.Point D.carrierVariety := D.pointEquiv.symm ⟨x, hxD⟩
      have hzI : fA.onPoints z ∈ IA := ⟨z, rfl⟩
      have : fA.onPoints z = 1 := Subgroup.mem_bot.mp (hbot ▸ hzI)
      have hamb := congrArg A.inclusion.onPoints this
      rw [Morphism.codRestrictClosedSubgroup_inclusion_apply] at hamb
      change (D.pointEquiv z).val = 1 at hamb
      rw [D.pointEquiv.apply_symm_apply] at hamb
      exact hamb
    · exact bot_le
  have hIAtop : IA.toSubgroup = ⊤ :=
    (hA.normal_subgroup_dichotomy IA hIAn hIAconn).resolve_left hIAbot
  have hAleD : A ≤ D := by
    intro x hx
    let y : Variety.Point A.carrierVariety := A.pointEquiv.symm ⟨x, hx⟩
    have hyI : y ∈ IA := by
      change y ∈ IA.toSubgroup
      rw [hIAtop]
      trivial
    change y ∈ fA.image at hyI
    rcases hyI with ⟨z, hz⟩
    have hamb := congrArg A.inclusion.onPoints hz
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply] at hamb
    have hzD : D.inclusion.onPoints z ∈ D := (D.pointEquiv z).property
    have hxy : x = D.inclusion.onPoints z := by
      change (A.pointEquiv y).val = D.inclusion.onPoints z
      rw [A.pointEquiv.apply_symm_apply]
      exact hamb.symm
    exact hxy.symm ▸ hzD
  have hAB : A ≤ B := fun _ hx => hDB (hAleD hx)
  -- Repeating the simple-group argument inside `B` turns the nontrivial
  -- connected intersection into all of `B` as well.
  have hBA : B ≤ A := by
    let fB := D.inclusion.codRestrictClosedSubgroup B
      (fun x => hDB (D.pointEquiv x).property)
    let IB := fB.imageClosedSubgroup
    have hIBn : IB.toSubgroup.Normal := by
      refine ⟨?_⟩
      intro x hx y
      change x ∈ fB.image at hx
      rcases hx with ⟨z, rfl⟩
      let yg : Variety.Point G := B.inclusion.onPoints y
      let zg : Variety.Point G := D.inclusion.onPoints z
      have hzD : zg ∈ D := (D.pointEquiv z).property
      have hcD : yg * zg * yg⁻¹ ∈ D := hDn.conj_mem zg hzD yg
      let w : Variety.Point D.carrierVariety := D.pointEquiv.symm ⟨yg * zg * yg⁻¹, hcD⟩
      refine ⟨w, B.inclusion_injective ?_⟩
      simp only [map_mul, map_inv]
      rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
      change D.inclusion.onPoints w = yg * zg * yg⁻¹
      change (D.pointEquiv w).val = yg * zg * yg⁻¹
      rw [D.pointEquiv.apply_symm_apply]
    have hIBconn : _root_.IsConnected (IB : Set (Variety.Point B.carrierVariety)) :=
      fB.imageClosedSubgroup_isConnected
        (ClosedSubgroup.carrierVariety_isConnected D hDconn)
    have hIBbot : IB.toSubgroup ≠ ⊥ := by
      intro hbot
      apply hne
      apply le_antisymm
      · intro x hx
        have hxD : x ∈ D := subset_closure hx
        let z : Variety.Point D.carrierVariety := D.pointEquiv.symm ⟨x, hxD⟩
        have hzI : fB.onPoints z ∈ IB := ⟨z, rfl⟩
        have hz1 : fB.onPoints z = 1 := Subgroup.mem_bot.mp (hbot ▸ hzI)
        have hamb := congrArg B.inclusion.onPoints hz1
        rw [Morphism.codRestrictClosedSubgroup_inclusion_apply] at hamb
        change (D.pointEquiv z).val = 1 at hamb
        rw [D.pointEquiv.apply_symm_apply] at hamb
        exact hamb
      · exact bot_le
    have hIBtop : IB.toSubgroup = ⊤ :=
      (hB.normal_subgroup_dichotomy IB hIBn hIBconn).resolve_left hIBbot
    intro x hx
    let y : Variety.Point B.carrierVariety := B.pointEquiv.symm ⟨x, hx⟩
    have hyI : y ∈ IB := by
      change y ∈ IB.toSubgroup
      rw [hIBtop]
      trivial
    change y ∈ fB.image at hyI
    rcases hyI with ⟨z, hz⟩
    have hamb := congrArg B.inclusion.onPoints hz
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply] at hamb
    have hzD : D.inclusion.onPoints z ∈ D := (D.pointEquiv z).property
    apply hDA
    have hxy : x = D.inclusion.onPoints z := by
      change (B.pointEquiv y).val = D.inclusion.onPoints z
      rw [B.pointEquiv.apply_symm_apply]
      exact hamb.symm
    exact hxy.symm ▸ hzD
  exact SetLike.coe_injective (Set.Subset.antisymm hAB hBA)

omit [IsAlgClosed k] in
private lemma exists_noncommuting_component
    {G : Variety k} [AlgebraicGroup G]
    {n m : ℕ} {components : Fin n → ClosedSubgroup G}
    {components' : Fin m → ClosedSubgroup G}
    (hfamily : IsSemisimpleComponentFamily components)
    (hfamily' : IsSemisimpleComponentFamily components') (i : Fin n) :
    ∃ j, ⁅(components i).toSubgroup, (components' j).toSubgroup⁆ ≠ ⊥ := by
  by_contra h
  push Not at h
  have hcomm : IsMulCommutative (Variety.Point (components i).carrierVariety) := by
    refine ⟨⟨?_⟩⟩
    intro x y
    apply (components i).inclusion_injective
    rcases hfamily'.factorization ((components i).inclusion.onPoints y) with
      ⟨factors, hfactors, hy⟩
    simp only [map_mul]
    rw [hy]
    apply Commute.list_prod_right
    intro z hz
    rw [List.mem_ofFn] at hz
    rcases hz with ⟨j, rfl⟩
    have hcentral := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h j)
    exact (Subgroup.mem_centralizer_iff.mp
      (hcentral ((components i).pointEquiv x).property)
      (factors j) (hfactors j)).symm
  exact (hfamily.simple i).2.1
    ((commutator_eq_bot_iff (Variety.Point (components i).carrierVariety)).mpr hcomm)

public theorem range_eq
    {G : Variety k} [AlgebraicGroup G]
    {n m : ℕ} {components : Fin n → ClosedSubgroup G}
    {components' : Fin m → ClosedSubgroup G}
    (hfamily : IsSemisimpleComponentFamily components)
    (hfamily' : IsSemisimpleComponentFamily components') :
    Set.range components = Set.range components' := by
  apply Set.Subset.antisymm
  · rintro A ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := exists_noncommuting_component hfamily hfamily' i
    exact ⟨j, (eq_of_commutator_ne_bot (components i) (components' j)
      (hfamily.simple i) (hfamily'.simple j)
      (hfamily.component_normal i) (hfamily'.component_normal j) hj).symm⟩
  · rintro B ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := exists_noncommuting_component hfamily' hfamily j
    exact ⟨i, (eq_of_commutator_ne_bot (components' j) (components i)
      (hfamily'.simple j) (hfamily.simple i)
      (hfamily'.component_normal j) (hfamily.component_normal i) hi).symm⟩

end IsSemisimpleComponentFamily
end Theory.AlgebraicGroup
