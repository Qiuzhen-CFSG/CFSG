module

public import Theory.GroupAction.CentralKernelFixedResidual
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# Components in fixed subgroups of central quotients

For an equivariant surjection with central kernel, the image of the upstairs
fixed subgroup is normal in the full downstairs fixed subgroup. A lift of a
fixed element has central displacement, so conjugation by that lift preserves
upstairs fixed points. Mapping a component's subnormal chain and ascending
through this normal image gives subnormality in the full fixed subgroup.
A centerless component meets the central kernel trivially, so its actual image
is isomorphic to it and remains quasisimple.

This generalizes the checked normal-image argument in the Chapter 15
QuotientCentralizer adapter, and supplies the quotient-component step in
Aschbacher–Smith 16.3.6, printed p.1179 / PDF p.1196 (1 March 2004 manuscript).
No equality between the two fixed subgroups is asserted.
-/

public section
open Subgroup Theory.GroupTheory
namespace MulAut
variable {G H : Type*} [Group G] [Group H]

/-- Central displacement makes the fixed-subgroup image normal in the full fixed subgroup. -/
theorem fixedSubgroupMap_range_normal_of_central_ker
    (a : MulAut G) (b : MulAut H) (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (heq : ∀ x, f (a x) = b (f x)) :
    (fixedSubgroupMap a b f heq).range.Normal := by
  refine ⟨?_⟩
  intro z hz y
  obtain ⟨k, rfl⟩ := hz
  obtain ⟨x, hx⟩ := hf (y : H)
  have hxc : a x * x⁻¹ ∈ center G := by
    apply hc
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, hx,
      (mem_fixedSubgroup _ _).mp y.property, mul_inv_cancel]
  have hk : a (x * (k : G) * x⁻¹) = x * (k : G) * x⁻¹ := by
    rw [map_mul, map_mul, map_inv, (mem_fixedSubgroup _ _).mp k.property]
    calc
      _ = (a x * x⁻¹) * (x * (k : G) * x⁻¹) * (a x * x⁻¹)⁻¹ := by group
      _ = _ := by
        rw [← mem_center_iff.mp hxc (x * (k : G) * x⁻¹)]
        group
  refine ⟨⟨x * (k : G) * x⁻¹, (mem_fixedSubgroup _ _).mpr hk⟩, ?_⟩
  apply Subtype.ext
  change f (x * (k : G) * x⁻¹) = (y : H) * f k * (y : H)⁻¹
  rw [map_mul, map_mul, map_inv, hx]

/-- A centerless fixed component survives with an actual isomorphism onto its image. -/
theorem fixedSubgroupMap_component_of_center_eq_bot
    (a : MulAut G) (b : MulAut H) (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (heq : ∀ x, f (a x) = b (f x))
    (K : Subgroup a.fixedSubgroup) (hK : IsComponent a.fixedSubgroup K)
    (hZ : center K = ⊥) :
    IsComponent b.fixedSubgroup (K.map (fixedSubgroupMap a b f heq)) ∧
      Nonempty (K ≃* K.map (fixedSubgroupMap a b f heq)) := by
  let g := fixedSubgroupMap a b f heq
  have hn : g.range.Normal := fixedSubgroupMap_range_normal_of_central_ker a b f hf hc heq
  have hi : Function.Injective (g.subgroupMap K) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_bot_iff.mp
    intro x hx
    have hfx : f ((x : a.fixedSubgroup) : G) = 1 :=
      congrArg (fun z : K.map g => ((z : b.fixedSubgroup) : H)) hx
    have hz : x ∈ center K := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      apply Subtype.ext
      exact mem_center_iff.mp (hc hfx) ((y : a.fixedSubgroup) : G)
    simpa only [hZ] using hz
  let e := MulEquiv.ofBijective (g.subgroupMap K) ⟨hi, g.subgroupMap_surjective K⟩
  have hsn : (K.map g).IsSubnormal := by
    have hs := (hK.1.map g.rangeRestrict_surjective).trans' hn.isSubnormal
    simpa only [map_map, MonoidHom.subtype_comp_rangeRestrict] using hs
  let := hK.2
  exact ⟨⟨hsn, IsQuasisimple.of_mulEquiv e⟩, ⟨e⟩⟩
end MulAut

namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

private theorem fixed_normal_preimage (a : MulAut G) (b : MulAut H)
    (f : G →* H) (hc : f.ker ≤ center G)
    (heq : ∀ x, f (a x) = b (f x)) :
    (a.fixedSubgroup.subgroupOf (b.fixedSubgroup.comap f)).Normal := by
  let P := b.fixedSubgroup.comap f
  have hdmem (x : P) : a x * (x : G)⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq]
    have hx := (MulAut.mem_fixedSubgroup _ _).mp x.property
    rw [hx, mul_inv_cancel]
  let d : P →* f.ker := {
    toFun x := ⟨a x * (x : G)⁻¹, hdmem x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change a ((x : G) * y) * ((x : G) * y)⁻¹ =
        (a x * (x : G)⁻¹) * (a y * (y : G)⁻¹)
      have hy := mem_center_iff.mp (hc (hdmem y)) (x : G)⁻¹
      rw [map_mul, mul_inv_rev]
      calc
        _ = a x * ((a y * (y : G)⁻¹) * (x : G)⁻¹) := by group
        _ = a x * ((x : G)⁻¹ * (a y * (y : G)⁻¹)) := by rw [hy]
        _ = _ := by group }
  have hk : d.ker = a.fixedSubgroup.subgroupOf P := by
    ext x
    change (⟨a x * (x : G)⁻¹, hdmem x⟩ : f.ker) = 1 ↔ _
    rw [Subtype.ext_iff]
    change a x * (x : G)⁻¹ = 1 ↔ (x : G) ∈ a.fixedSubgroup
    rw [MulAut.mem_fixedSubgroup]
    exact mul_inv_eq_one
  exact hk ▸ inferInstance

/-- A nontrivial component image remains a component of the full fixed subgroup
under an equivariant central quotient. -/
theorem IsComponentIn.map_fixed_of_central_ker {K : Subgroup G}
    (a : MulAut G) (b : MulAut H) (f : G →* H)
    (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (heq : ∀ x, f (a x) = b (f x))
    (hK : IsComponentIn K a.fixedSubgroup) (hne : K.map f ≠ ⊥) :
    IsComponentIn (K.map f) b.fixedSubgroup := by
  let P := b.fixedSubgroup.comap f
  have hC : a.fixedSubgroup ≤ P := by
    intro x hx
    change f x ∈ b.fixedSubgroup
    rw [MulAut.mem_fixedSubgroup]
    rw [← heq, (MulAut.mem_fixedSubgroup _ _).mp hx]
  have hn := fixed_normal_preimage a b f hc heq
  have hKP := hK.of_subnormal hC hn.isSubnormal
  let q : P →* b.fixedSubgroup :=
    (f.comp P.subtype).codRestrict b.fixedSubgroup (fun x => x.property)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨⟨x, by change f x ∈ b.fixedSubgroup; rw [hx]; exact y.property⟩,
      Subtype.ext hx⟩
  have he : (K.subgroupOf P).map q = (K.map f).subgroupOf b.fixedSubgroup := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hKP.1 hy⟩, hy, Subtype.ext hxy⟩
  have hle : K.map f ≤ b.fixedSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKP.1 hx
  refine ⟨hle, ?_⟩
  rcases hKP.2.map_surjective q hq with hb | h
  · have hh := congrArg (Subgroup.map b.fixedSubgroup.subtype) (he.symm.trans hb)
    rw [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at hh
    exact (hne hh).elim
  · exact he ▸ h

end Theory.GroupTheory
