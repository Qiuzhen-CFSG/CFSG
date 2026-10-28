module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.Transport

/-!
# Projecting components of an HS cover's fixed subgroup

The map from a fixed subgroup of I to the fixed subgroup in I/O₂(I) need
not be surjective. Its image is nevertheless normal: a lift of a fixed
quotient element changes under the automorphism only by a central element,
which does not change its conjugation on fixed elements.

The kernel is central. Hence a quasisimple component has nontrivial image;
that image is a component of the full quotient fixed subgroup by normality
of the image. This supplies the component transport needed before applying
the HS centralizer table, without conflating the two fixed subgroups.

Source application: Aschbacher–Smith, 16.1.5(10), 16.1.7(3h), and 16.3.5,
printed pp.1172–1173 and 1179.
-/

public section


namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- Restrict the actual quotient projection to fixed elements. -/
@[expose] def fixedProjection (I : Subgroup G)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) (r : MulAut I) :
    r.fixedSubgroup →* (modelAction I e r).fixedSubgroup :=
  ((modelProjection I e).comp r.fixedSubgroup.subtype).codRestrict _ (fun x => by
    rw [MulAut.mem_fixedSubgroup]
    change modelAction I e r (modelProjection I e x) = modelProjection I e x
    rw [modelAction_projection, (MulAut.mem_fixedSubgroup r x).mp x.property])

/-- The image is normal even when not every quotient fixed point lifts. -/
theorem fixedProjection_range_normal (I : Subgroup G)
    (hz : pCore 2 I ≤ center I)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) (r : MulAut I) :
    (fixedProjection I e r).range.Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ g
  obtain ⟨y, hy⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 I))) g.val
  have hy' : modelProjection I e y = g.val := hy
  have hq : modelProjection I e (r y) = modelProjection I e y := by
    rw [← modelAction_projection, hy']
    exact (MulAut.mem_fixedSubgroup _ _).mp g.property
  have hc : y⁻¹ * r y ∈ center I := hz (QuotientGroup.eq.mp (e.injective hq).symm)
  have hfix : r (y * x.val * y⁻¹) = y * x.val * y⁻¹ := by
    rw [map_mul, map_mul, map_inv, (MulAut.mem_fixedSubgroup r x).mp x.property]
    calc
      r y * x.val * (r y)⁻¹ = y * ((y⁻¹ * r y) * x.val) * (r y)⁻¹ := by group
      _ = y * (x.val * (y⁻¹ * r y)) * (r y)⁻¹ := by
        rw [← mem_center_iff.mp hc x.val]
      _ = y * x.val * y⁻¹ := by group
  refine ⟨⟨y * x.val * y⁻¹, (MulAut.mem_fixedSubgroup r _).mpr hfix⟩, ?_⟩
  apply Subtype.ext
  change modelProjection I e (y * x.val * y⁻¹) =
    g.val * modelProjection I e x.val * g.val⁻¹
  rw [map_mul, map_mul, map_inv, hy']

/-- Restriction of a central quotient retains a central kernel. -/
theorem fixedProjection_ker_le_center (I : Subgroup G)
    (hz : pCore 2 I ≤ center I)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) (r : MulAut I) :
    (fixedProjection I e r).ker ≤ center r.fixedSubgroup := by
  intro x hx
  have he : modelProjection I e x = 1 := congrArg Subtype.val hx
  have hq : QuotientGroup.mk' (pCore 2 I) x.val = 1 := by
    apply e.injective
    rw [map_one]
    exact he
  have hz' := hz ((QuotientGroup.eq_one_iff x.val).mp hq)
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (mem_center_iff.mp hz' y.val)

/-- Every component maps to a component of the full quotient fixed subgroup. -/
theorem fixedProjection_component (I : Subgroup G)
    (hz : pCore 2 I ≤ center I)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) (r : MulAut I)
    (K : Subgroup r.fixedSubgroup) (hK : IsComponent r.fixedSubgroup K) :
    IsComponent (modelAction I e r).fixedSubgroup (K.map (fixedProjection I e r)) := by
  let f := fixedProjection I e r
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hne : K.map f ≠ ⊥ := by
    intro he
    have hkc : K ≤ center r.fixedSubgroup :=
      (show K ≤ f.ker from map_le_iff_le_comap.mp he.le).trans
        (fixedProjection_ker_le_center I hz e r)
    have hcomm : IsMulCommutative K :=
      ⟨⟨fun x y => Subtype.ext (mem_center_iff.mp (hkc y.property) x.val)⟩⟩
    exact Group.IsPerfect.not_isMulCommutative K hcomm
  let : Nontrivial (K.map f) := (nontrivial_iff_ne_bot _).mpr hne
  have hnormal := fixedProjection_range_normal I hz e r
  have hsub := (hK.1.map f.rangeRestrict_surjective).trans' hnormal.isSubnormal
  have he : (K.map f.rangeRestrict).map f.range.subtype = K.map f := by
    rw [map_map]
    rfl
  exact ⟨he ▸ hsub, IsQuasisimple.of_surjective (f.subgroupMap K) (f.subgroupMap_surjective K)⟩

/-- The original relative component has a component image in the quotient
fixed subgroup. Its ambient image is exactly the canonical projection of L,
so later table arguments retain the actual embedding. -/
theorem Configuration.exists_projected_component [Finite G] {𝒦 : GroupClass}
    {E L I : Subgroup G} {a i : G} (h : Configuration 𝒦 E L I a i)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    ∃ J : Subgroup (quotientAction E I h.normalizes e ⟨a, h.actor_mem⟩).fixedSubgroup,
      IsComponent _ J ∧
        J.map (quotientAction E I h.normalizes e ⟨a, h.actor_mem⟩).fixedSubgroup.subtype =
          (L.subgroupOf I).map (modelProjection I e) := by
  let r := inducedAction E I h.normalizes ⟨a, h.actor_mem⟩
  let C := I ⊓ involutionCentralizer a
  let f : C ≃* r.fixedSubgroup :=
    ComponentTransfer.Intrinsic.centralizerEquivFixed (h.normalizes h.actor_mem)
  let K := (L.subgroupOf C).map f.toMonoidHom
  have hK : IsComponent r.fixedSubgroup K := h.relative_component.2.map_equiv f
  refine ⟨K.map (fixedProjection I e r),
    fixedProjection_component I h.center_eq_core.ge e r K hK, ?_⟩
  change ((L.subgroupOf C).map f.toMonoidHom |>.map (fixedProjection I e r)).map
    (modelAction I e r).fixedSubgroup.subtype = _
  rw [map_map, map_map]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.val, y.property.1⟩, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.val, h.relative_component.1 hy⟩, hy, rfl⟩


end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
