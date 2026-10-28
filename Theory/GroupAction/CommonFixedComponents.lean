module
public import Theory.GroupAction.FixedPointHom
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# Components in common fixed groups through two successive kernels

For an equivariant surjection with central kernel, the image of the common
fixed group is normal in the downstairs common fixed group: every lift of a
fixed element has central displacement. A preceding quotient with kernel
prime to a p-group actor is surjective on fixed points. Thus a normal seed
whose image is quasisimple maps to an ordinary component of the common
fixed group through the two quotients. Neither the central kernel nor the
whole actor is replaced by a selected element.

The application is the literal double quotient in the odd-local comparison
of Aschbacher--Smith 4.4.3, printed p.623. Coprime lifting is the fiber argument
of GLS II, Lemma 4.2(i), as implemented in FixedPointHom.
-/

public section
open Subgroup Theory.GroupTheory
namespace FixedPoints
variable {A G H J : Type*} [Group A] [Group G] [Group H] [Group J]
  [MulDistribMulAction A G] [MulDistribMulAction A H] [MulDistribMulAction A J]

/-- Central displacement preserves all common fixed points under conjugation. -/
theorem mapHom_range_normal_of_central_kernel
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (he : ∀ (a : A) (x : G), f (a • x) = a • f x) :
    (mapHom f he).range.Normal := by
  refine ⟨?_⟩
  intro z hz y
  obtain ⟨k,rfl⟩ := hz
  obtain ⟨x,hx⟩ := hf (y : H)
  have hk : x * (k : G) * x⁻¹ ∈ fixedPointSubgroup A G := by
    intro a
    have hxc : (a • x) * x⁻¹ ∈ center G := by
      apply hc
      rw [MonoidHom.mem_ker,map_mul,map_inv,he,hx,y.property a,mul_inv_cancel]
    simp only [smul_mul',smul_inv',k.property a]
    calc
      _ = ((a • x) * x⁻¹) * (x * (k : G) * x⁻¹) * ((a • x) * x⁻¹)⁻¹ := by group
      _ = _ := by
        rw [←mem_center_iff.mp hxc (x * (k : G) * x⁻¹)]
        group
  refine ⟨⟨_,hk⟩,?_⟩
  apply Subtype.ext
  change f (x * (k : G) * x⁻¹) = (y : H) * f k * (y : H)⁻¹
  rw [map_mul,map_mul,map_inv,hx]

/-- A coprime first kernel and central second kernel preserve a normal image
of the common fixed group, without discarding the central covering kernel. -/
theorem mapHom_range_normal_of_coprime_central_kernel [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p A)
    (f : G →* H) (hf : Function.Surjective f)
    (he : ∀ (a : A) (x : G), f (a • x) = a • f x)
    (hk : ¬ p ∣ Nat.card f.ker)
    (g : H →* J) (hg : Function.Surjective g) (hc : g.ker ≤ center H)
    (he' : ∀ (a : A) (x : H), g (a • x) = a • g x) :
    (mapHom (A := A) (g.comp f) (fun (a : A) (x : G) => by simp only [MonoidHom.comp_apply,he,he'])).range.Normal := by
  have hs := mapHom_surjective_of_coprime_kernel hp f hf he hk
  have hn := mapHom_range_normal_of_central_kernel g hg hc he'
  have hr : (mapHom (A := A) (g.comp f) (fun (a : A) (x : G) => by simp only [MonoidHom.comp_apply,he,he'])).range =
      (mapHom g he').range := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨mapHom f he y,rfl⟩
    · rintro ⟨y,rfl⟩
      obtain ⟨z,rfl⟩ := hs y
      exact ⟨z,rfl⟩
  exact hr ▸ hn

/-- A quasisimple image of a normal seed is a component of the whole common
fixed group when the fixed-point map has normal image. -/
theorem component_image_of_normal_fixed_image
    (f : G →* H) (he : ∀ (a : A) (x : G), f (a • x) = a • f x)
    (hn : (mapHom f he).range.Normal)
    (B : Subgroup G) (hB : B ≤ fixedPointSubgroup A G)
    (hBn : (B.subgroupOf (fixedPointSubgroup A G)).Normal)
    (hqs : IsQuasisimple (B.map f)) :
    IsComponentIn (B.map f) (fixedPointSubgroup A H) := by
  let C := fixedPointSubgroup A G
  let D := fixedPointSubgroup A H
  let q := mapHom f he
  have hBD : B.map f ≤ D := by
    rintro _ ⟨b,hb,rfl⟩ a
    rw [←he,hB hb a]
  have hm : (B.subgroupOf C).map q = (B.map f).subgroupOf D := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b,hb,rfl⟩
    · rintro ⟨b,hb,hbx⟩
      exact ⟨⟨b,hB hb⟩,hb,Subtype.ext hbx⟩
  refine ⟨hBD,?_,?_⟩
  · have hs := (hBn.isSubnormal.map q.rangeRestrict_surjective).trans' hn.isSubnormal
    have hs' : ((B.subgroupOf C).map q).IsSubnormal := by
      simpa only [map_map,MonoidHom.subtype_comp_rangeRestrict] using hs
    exact hm ▸ hs'
  · let := hqs
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hBD).symm
end FixedPoints
