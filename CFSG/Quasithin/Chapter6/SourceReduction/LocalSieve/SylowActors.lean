module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.ActionEscape

/-!
# The original Cartan and its full Sylow action

T normalizes the local Borel, whose Hall supplement is the original Cartan.
Factoring Borel elements on both sides proves AT=TA without assuming that
T normalizes A. Intersecting with a Sylow overgroup and applying its actual
homomorphism preserve this product identity. The same normalized Borel
product proves solvability of the resulting Sylow join.

These supply the literal Sylow and solvability premises for the cyclic-actor
sieve in 5.1.13. In the automorphism application the Sylow lies in the
induced action group, not in the whole automorphism group.
Source: Aschbacher--Smith Notation 5.1.9 and 5.1.13, printed pp.634,636.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sylow_normalizes_borel {T : Sylow 2 G} {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) := by
  have hTI : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer hTL).trans inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) :=
    (le_inf hTL (hTI.trans (normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact hTN

/-- The original Hall Cartan permutes with the full Sylow subgroup. -/
theorem CartanPair.left_permutes_sylow
    {T : Sylow 2 G} {L H A B : Subgroup G}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) := by
  have hTN := sylow_normalizes_borel hTL
  obtain ⟨S,hS⟩ := exists_sylow_localBorel T L hTL
  have hc := OddHall.sylow_complement_of_hall S c.left_hall
  have left_factor (b : G) (hb : b ∈ localBorel T L) :
      ∃ s ∈ (T : Subgroup G), ∃ a ∈ A, s * a = b := by
    obtain ⟨⟨s,a⟩,he⟩ := hc.2 ⟨b,hb⟩
    have hs : (s.val : G) ∈ (T : Subgroup G) ⊓ L :=
      hS ▸ mem_map_of_mem (localBorel T L).subtype s.property
    exact ⟨s.val,hs.1,a.val,a.property,congrArg Subtype.val he⟩
  have right_factor (b : G) (hb : b ∈ localBorel T L) :
      ∃ a ∈ A, ∃ s ∈ (T : Subgroup G), a * s = b := by
    obtain ⟨⟨a,s⟩,he⟩ := hc.symm.2 ⟨b,hb⟩
    have hs : (s.val : G) ∈ (T : Subgroup G) ⊓ L :=
      hS ▸ mem_map_of_mem (localBorel T L).subtype s.property
    exact ⟨a.val,a.property,s.val,hs.1,congrArg Subtype.val he⟩
  apply Set.Subset.antisymm
  · rintro x ⟨a,ha,t,ht,rfl⟩
    have hb : t⁻¹ * a * t ∈ localBorel T L := by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp (hTN ((T : Subgroup G).inv_mem ht)) a).mp (c.left_le ha)
    obtain ⟨s,hs,b,hb',he⟩ := left_factor _ hb
    refine ⟨t*s,(T : Subgroup G).mul_mem ht hs,b,hb',?_⟩
    calc (t*s)*b = t*(s*b) := mul_assoc _ _ _
         _ = a*t := by rw [he]; group
  · rintro x ⟨t,ht,a,ha,rfl⟩
    have hb : t*a*t⁻¹ ∈ localBorel T L :=
      (mem_normalizer_iff.mp (hTN ht) a).mp (c.left_le ha)
    obtain ⟨b,hb',s,hs,he⟩ := right_factor _ hb
    refine ⟨b,hb',s*t,(T : Subgroup G).mul_mem hs ht,?_⟩
    calc b*(s*t) = (b*s)*t := (mul_assoc _ _ _).symm
         _ = t*a := by rw [he]; group

/-- Intersecting the Cartan with the original Sylow overgroup preserves permutability. -/
theorem CartanPair.intersection_permutes_sylow
    {T : Sylow 2 G} {L H A B Y : Subgroup G}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (hTY : (T : Subgroup G) ≤ Y) :
    ((A ⊓ Y : Subgroup G) : Set G) * (T : Set G) =
      (T : Set G) * ((A ⊓ Y : Subgroup G) : Set G) := by
  have he := c.left_permutes_sylow hTL
  apply Set.Subset.antisymm
  · rintro x ⟨a,ha,t,ht,rfl⟩
    have hx : a*t ∈ (T : Set G) * (A : Set G) := he ▸ Set.mul_mem_mul ha.1 ht
    obtain ⟨s,hs,b,hb,hx⟩ := hx
    have hbY : b ∈ Y := by
      have hh := Y.mul_mem (Y.inv_mem (hTY hs)) (Y.mul_mem ha.2 (hTY ht))
      rw [←hx,inv_mul_cancel_left] at hh
      exact hh
    exact ⟨s,hs,b,⟨hb,hbY⟩,hx⟩
  · rintro x ⟨t,ht,a,ha,rfl⟩
    have hx : t*a ∈ (A : Set G) * (T : Set G) := he.symm ▸ Set.mul_mem_mul ht ha.1
    obtain ⟨b,hb,s,hs,hx⟩ := hx
    have hbY : b ∈ Y := by
      have hh := Y.mul_mem (Y.mul_mem (hTY ht) ha.2) (Y.inv_mem (hTY hs))
      rw [←hx,mul_inv_cancel_right] at hh
      exact hh
    exact ⟨b,⟨hb,hbY⟩,s,hs,hx⟩

/-- The literal image of the Cartan intersection permutes with the literal Sylow image. -/
theorem CartanPair.image_intersection_permutes_sylow
    {T : Sylow 2 G} {L H A B Y : Subgroup G}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (hTY : (T : Subgroup G) ≤ Y)
    {Q : Type*} [Group Q] (f : Y →* Q) :
    ((A.subgroupOf Y).map f : Set Q) * (((T : Subgroup G).subgroupOf Y).map f : Set Q) =
      (((T : Subgroup G).subgroupOf Y).map f : Set Q) * ((A.subgroupOf Y).map f : Set Q) := by
  have he := c.intersection_permutes_sylow hTL hTY
  apply Set.Subset.antisymm
  · rintro x ⟨_,⟨a,ha,rfl⟩,_,⟨t,ht,rfl⟩,rfl⟩
    have hh : (a:G)*(t:G) ∈ (T : Set G) * ((A ⊓ Y : Subgroup G) : Set G) :=
      he ▸ Set.mul_mem_mul (show (a:G) ∈ A ⊓ Y from ⟨ha,a.property⟩) ht
    obtain ⟨s,hs,b,hb,hh⟩ := hh
    change b ∈ A ∧ b ∈ Y at hb
    refine ⟨f ⟨s,hTY hs⟩,mem_map_of_mem f hs,
      f ⟨b,hb.2⟩,mem_map_of_mem f hb.1,?_⟩
    exact (f.map_mul _ _).symm.trans ((congrArg f (Subtype.ext hh)).trans (f.map_mul _ _))
  · rintro x ⟨_,⟨t,ht,rfl⟩,_,⟨a,ha,rfl⟩,rfl⟩
    have hh : (t:G)*(a:G) ∈ ((A ⊓ Y : Subgroup G) : Set G) * (T : Set G) :=
      he.symm ▸ Set.mul_mem_mul ht (show (a:G) ∈ A ⊓ Y from ⟨ha,a.property⟩)
    obtain ⟨b,hb,s,hs,hh⟩ := hh
    change b ∈ A ∧ b ∈ Y at hb
    refine ⟨f ⟨b,hb.2⟩,mem_map_of_mem f hb.1,
      f ⟨s,hTY hs⟩,mem_map_of_mem f hs,?_⟩
    exact (f.map_mul _ _).symm.trans ((congrArg f (Subtype.ext hh)).trans (f.map_mul _ _))

/-- The source Cartan intersection and full Sylow generate a solvable group. -/
theorem Input.cartan_intersection_sylow_isSolvable
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input κ T L W n) (c : CartanPair T L H A B) :
    Group.IsSolvable ((A ⊓ Y) ⊔ (T : Subgroup G) : Subgroup G) := by
  let : Group.IsSolvable (localBorel T L) :=
    localBorel_isSolvable h.exponent h.linear h.sylow_normalizes
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable (localBorel T L ⊔ (T : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes _ _ (sylow_normalizes_borel h.sylow_normalizes)
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective
    (sup_le_sup (inf_le_left.trans c.left_le) le_rfl))

/-- Solvability survives the literal quotient action and restriction to Y. -/
theorem Input.cartan_sylow_action_isSolvable
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input κ T L W n) (c : CartanPair T L H A B)
    (hTY : (T : Subgroup G) ≤ Y) {Q : Type*} [Group Q] (f : Y →* Q) :
    Group.IsSolvable ((A.subgroupOf Y).map f ⊔
      ((T : Subgroup G).subgroupOf Y).map f : Subgroup Q) := by
  let J := (A ⊓ Y) ⊔ (T : Subgroup G)
  let P := A.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y
  let : Group.IsSolvable J := h.cartan_intersection_sylow_isSolvable c
  have hmap : P.map Y.subtype ≤ J := by
    rw [Subgroup.map_sup,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hTY]
  let : Group.IsSolvable (P.map Y.subtype) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hmap)
  let : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective
    (f := (P.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
    (P.equivMapOfInjective Y.subtype Y.subtype_injective).injective
  have hs : Group.IsSolvable (P.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective P)
  change Group.IsSolvable ((A.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y).map f) at hs
  rwa [Subgroup.map_sup] at hs

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
