module

public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.GroupTheory.Nilpotent

/-!
# Abelian prime subgroups through central coprime kernels

The inverse image of an abelian subgroup under a central extension is
nilpotent. Its Sylow p-subgroup is characteristic in that inverse image.
When the kernel has order prime to p, this Sylow subgroup maps isomorphically
onto the given p-subgroup. Every lift of a normalizing element therefore
normalizes the chosen subgroup. This is the relative normality needed to
transport centralizers and their normalizer indices.

Source: the passage from special to projective groups in Aschbacher--Smith,
A.3.21(c), printed pp.55--56 of refs/quasithin.pdf.
-/

namespace Subgroup
open scoped IsMulCommutative

/-- An abelian p-subgroup has an abelian lift invariant under the full inverse
image of its normalizer through a central kernel of order prime to p. -/
public theorem exists_abelian_prime_lift_of_central_coprime_kernel {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (hcop : Nat.Coprime p (Nat.card f.ker))
    (B : Subgroup H) [IsMulCommutative B] (hB : IsPGroup p B) :
    ∃ Q : Subgroup G, IsPGroup p Q ∧ IsMulCommutative Q ∧ Q.map f = B ∧
      (normalizer B).comap f ≤ normalizer Q := by
  let R := B.comap f
  let g : R →* B := f.subgroupComap B
  have hg : Function.Surjective g := f.subgroupComap_surjective_of_surjective B hf
  have hgc : g.ker ≤ center R := by
    intro x hx
    have hxk : (x : G) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hc hxk) y)
  let _ : Group.IsNilpotent R := Subgroup.isNilpotent_of_ker_le_center g hgc
  let P : Sylow p R := Sylow.nonempty.some
  let _ : (P : Subgroup R).Characteristic := P.characteristic_of_normal inferInstance
  have hPtop : (P.mapSurjective hg : Subgroup B) = ⊤ := by
    apply top_unique
    exact (hB.to_subgroup ⊤).le_sylow_of_normal _
  let Q : Subgroup G := (P : Subgroup R).map R.subtype
  have hQp : IsPGroup p Q := P.isPGroup'.map R.subtype
  have hQmap : Q.map f = B := by
    have hh := congrArg (Subgroup.map B.subtype) hPtop
    change ((P : Subgroup R).map g).map B.subtype = (⊤ : Subgroup B).map B.subtype at hh
    rw [map_map, ← MonoidHom.range_eq_map, range_subtype] at hh
    change (P : Subgroup R).map (f.comp R.subtype) = B at hh
    simpa only [Q, map_map] using hh
  have hQi := injective_comp_subtype_of_coprime_ker f hcop Q hQp
  have hQa : IsMulCommutative Q := by
    refine ⟨⟨fun x y => hQi ?_⟩⟩
    have hx : f (x : G) ∈ B := hQmap ▸ mem_map_of_mem f x.property
    have hy : f (y : G) ∈ B := hQmap ▸ mem_map_of_mem f y.property
    have hh := congrArg Subtype.val (mul_comm' (⟨f x, hx⟩ : B) ⟨f y, hy⟩)
    change f (x : G) * f (y : G) = f (y : G) * f (x : G) at hh
    simpa only [MonoidHom.comp_apply, map_mul, Subgroup.subtype_apply] using hh
  refine ⟨Q, hQp, hQa, hQmap, ?_⟩
  apply le_trans ?_ (normalizer_le_normalizer_characteristic_image R (P : Subgroup R))
  exact le_of_eq (comap_normalizer_eq_of_surjective B hf)


/-- On the normalizer of a subgroup, injectivity on that subgroup detects
centralizing from the image. No ambient normality is assumed. -/
public theorem centralizer_image_mem_iff_of_injective_on_subgroup {G H : Type*} [Group G] [Group H]
    (f : G →* H) (Q : Subgroup G)
    (hi : Function.Injective (f.comp Q.subtype))
    {x : G} (hx : x ∈ normalizer Q) :
    f x ∈ centralizer (Q.map f : Set H) ↔ x ∈ centralizer (Q : Set G) := by
  constructor
  · intro hc q hq
    have hn : x * q * x⁻¹ ∈ Q := (mem_normalizer_iff.mp hx q).mp hq
    have he : (⟨x * q * x⁻¹, hn⟩ : Q) = ⟨q, hq⟩ := by
      apply hi
      change f (x * q * x⁻¹) = f q
      rw [map_mul, map_mul, map_inv, ← hc (f q) (mem_map_of_mem f hq)]
      simp only [mul_inv_cancel_right]
    exact ((mul_inv_eq_iff_eq_mul).mp (congrArg Subtype.val he)).symm
  · intro hc y hy
    obtain ⟨q, hq, rfl⟩ := hy
    simpa only [map_mul] using congrArg f (hc q hq)

/-- If all lifts of normalizing elements normalize the subgroup, both the
centralizer and its relative normalizer index transport through the surjection. -/
public theorem centralizer_map_and_relIndex_eq_of_normalizer_preimage {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (Q : Subgroup G)
    (hi : Function.Injective (f.comp Q.subtype))
    (hn : (normalizer (Q.map f)).comap f ≤ normalizer Q) :
    (centralizer (Q : Set G)).map f = centralizer (Q.map f : Set H) ∧
    (centralizer (Q : Set G)).relIndex (normalizer Q) =
      (centralizer (Q.map f : Set H)).relIndex (normalizer (Q.map f)) := by
  have hN : (normalizer Q).map f = normalizer (Q.map f) := by
    apply le_antisymm (Q.le_normalizer_map f)
    intro y hy
    obtain ⟨x, rfl⟩ := hf y
    exact mem_map.mpr ⟨x, hn hy, rfl⟩
  constructor
  · apply le_antisymm (map_centralizer_le_centralizer_image (Q : Set G) f)
    intro y hy
    obtain ⟨x, rfl⟩ := hf y
    exact mem_map.mpr ⟨x, (centralizer_image_mem_iff_of_injective_on_subgroup f Q hi
      (hn (centralizer_le_normalizer _ hy))).mp hy, rfl⟩
  · have he : (centralizer (Q : Set G)).subgroupOf (normalizer Q) =
        ((centralizer (Q.map f : Set H)).comap f).subgroupOf (normalizer Q) := by
      ext x
      exact (centralizer_image_mem_iff_of_injective_on_subgroup f Q hi x.property).symm
    change ((centralizer (Q : Set G)).subgroupOf (normalizer Q)).index = _
    rw [he]
    exact ((centralizer (Q.map f : Set H)).relIndex_comap f (normalizer Q)).trans
      (congrArg ((centralizer (Q.map f : Set H)).relIndex) hN)

end Subgroup
