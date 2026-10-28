module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.FFModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.Overgroups
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.PermutationTransport
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Local inputs and quotient geometry for the Lie-model inspection

The common Sylow subgroup maps to a Sylow subgroup of the actual action
quotient. Its intersection with the normal component is a Sylow subgroup
of that component. The intersection with M is proper and is the unique
largest proper S-invariant component subgroup containing Y₊* and S* ∩ L*.

The prime-to-three residual of M ∩ L is Y₊; this identity survives the
original star map. Every three-subgroup of M_I* has order at most three,
using the S₃ shadow before passing to the quotient. No Borel, parabolic,
field restriction, model equivalence or diagram action is assumed here.
Those constructions remain the model-inspection obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.26–28, printed pp.1130–1131 (PDF pp.1147–1148).
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
variable {G : Type*} [Group G]

/-- Earlier source inputs, with the actual common Sylow witness. This record
contains no model-classification or parabolic conclusion. -/
structure Input (d : LocalData G) (I : Subgroup G) (c : ComponentWitness d I) where
  minimal : I ∈ d.HplusMinimal
  characteristicTwo : HasCharacteristicTwo I
  rank : primeRank 3 d.Yplus = 1
  facts : RankOneFacts d I
  solvableControl : SolvableInvariantControl d I
  normal : (c.L.subgroupOf I).Normal
  contains : d.Yplus ≤ c.L
  sylow : Sylow 2 I
  sylow_eq : (sylow : Subgroup I).map I.subtype = d.S
  module_le : d.V ≤ (d.T : Subgroup G)
  kernel_le : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I

/-- The embedded residual commutes with the original star map. -/
theorem starImage_embedded_residual [Finite G] (d : LocalData G)
    {I X : Subgroup G} (hXI : X ≤ I) :
    d.starImage I ((primeToResidual 3 X).map X.subtype) =
      (primeToResidual 3 (d.starImage I X)).map (d.starImage I X).subtype := by
  have he := map_embedded_primeToResidual_of_hom 3 (X.subgroupOf I) I.subtype
  rw [map_subgroupOf_eq_of_le hXI] at he
  have hpre : ((primeToResidual 3 X).map X.subtype).subgroupOf I =
      (primeToResidual 3 (X.subgroupOf I)).map (X.subgroupOf I).subtype := by
    rw [← he]
    exact comap_map_eq_self_of_injective I.subtype_injective _
  change (((primeToResidual 3 X).map X.subtype).subgroupOf I).map (d.starMap I) = _
  rw [hpre, map_embedded_primeToResidual_of_hom]
  rfl

namespace Input
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
variable (a : Input d I c)
include a

theorem sylow_le : d.S ≤ I := a.sylow_eq ▸ map_subtype_le _

theorem yplus_le_intersection : d.Yplus ≤ d.MI I :=
  a.facts.residual ▸ map_subtype_le _

theorem componentStar_normal : (d.starImage I c.L).Normal :=
  a.normal.map (d.starMap I) (QuotientGroup.mk'_surjective _)

theorem intersectionStar_eq_inf : d.starImage I (d.M ⊓ c.L) =
    d.starImage I c.L ⊓ d.starImage I (d.MI I) :=
  component_intersection_star_eq_inf d c a.kernel_le

theorem star_kernel_le : (d.starMap I).ker ≤ (d.MI I).subgroupOf I := by
  rw [show (d.starMap I).ker = localActionKernel d.Z I from QuotientGroup.ker_mk' _]
  exact fun x hx => a.kernel_le ⟨x.property, hx⟩

variable [Finite G]

theorem generated : I = c.L ⊔ d.S :=
  (lemma_15_3_27_4_of_containment d a.minimal c a.sylow a.sylow_eq a.contains
    (a.yplus_le_intersection.trans inf_le_left)).1

theorem star_generated : d.starImage I c.L ⊔ d.starImage I d.S = ⊤ := by
  change (c.L.subgroupOf I).map (d.starMap I) ⊔
    (d.S.subgroupOf I).map (d.starMap I) = ⊤
  rw [← Subgroup.map_sup, ← subgroupOf_sup (component_le c) a.sylow_le, ← a.generated,
    subgroupOf_self]
  exact map_top_of_surjective (d.starMap I) (QuotientGroup.mk'_surjective _)

/-- The quotient Sylow is the image of the specified common Sylow. -/
noncomputable def starSylow : Sylow 2 (d.Star I) :=
  a.sylow.mapSurjective (QuotientGroup.mk'_surjective _)

theorem starSylow_coe : (a.starSylow : Subgroup (d.Star I)) = d.starImage I d.S := by
  change (a.sylow : Subgroup I).map (d.starMap I) = _
  rw [← a.sylow_eq]
  change _ = (((a.sylow : Subgroup I).map I.subtype).comap I.subtype).map _
  rw [comap_map_eq_self_of_injective I.subtype_injective]

/-- The actual Sylow intersection, intrinsically inside L*. -/
theorem exists_componentSylow : ∃ Q : Sylow 2 (d.starImage I c.L),
    (Q : Subgroup (d.starImage I c.L)) =
      (d.starImage I d.S).subgroupOf (d.starImage I c.L) := by
  let := a.componentStar_normal
  obtain ⟨Q, hQ⟩ := a.starSylow.exists_subgroupOf_eq_of_normal (d.starImage I c.L)
  exact ⟨Q, hQ.trans (congrArg (fun H => H.subgroupOf (d.starImage I c.L))
    a.starSylow_coe)⟩

omit [Finite G] in
theorem intersectionStar_ne_top : d.starImage I (d.MI I) ≠ ⊤ := by
  intro ht
  have he : (d.MI I).subgroupOf I = ⊤ := by
    have he := congrArg (fun H : Subgroup (d.Star I) => H.comap (d.starMap I)) ht
    change (((d.MI I).subgroupOf I).map (d.starMap I)).comap (d.starMap I) =
      (⊤ : Subgroup (d.Star I)).comap (d.starMap I) at he
    rwa [comap_map_eq_self a.star_kernel_le, comap_top] at he
  apply a.minimal.1.2
  intro x hx
  exact (show (⟨x, hx⟩ : I) ∈ (d.MI I).subgroupOf I from he ▸ mem_top _).1

theorem componentIntersectionStar_lt : d.starImage I (d.M ⊓ c.L) < d.starImage I c.L := by
  apply lt_of_le_of_ne (map_mono (comap_mono inf_le_right))
  intro he
  change d.starImage I (d.M ⊓ c.L) = d.starImage I c.L at he
  apply a.intersectionStar_ne_top
  rw [intersection_star_eq_component_intersection_sup d c a.normal a.generated,
    he, a.star_generated]

omit [Finite G] in
/-- S preserves the literal component intersection in the star quotient. -/
theorem sylow_normalizes_componentIntersectionStar :
    d.starImage I d.S ≤ normalizer (d.starImage I (d.M ⊓ c.L) : Set (d.Star I)) := by
  let := a.componentStar_normal
  rw [a.intersectionStar_eq_inf]
  have hSL : d.starImage I d.S ≤ normalizer (d.starImage I c.L : Set (d.Star I)) :=
    le_normalizer_of_normal
  have hSM : d.starImage I d.S ≤ d.starImage I (d.MI I) :=
    map_mono (comap_mono (le_inf (inf_le_left.trans d.sylow_le) a.sylow_le))
  exact (le_inf hSL (hSM.trans (d.starImage I (d.MI I)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- Any proper invariant component overgroup of the two specified subgroups
lies in the actual component intersection. -/
theorem invariant_component_overgroup_le (H : Subgroup (d.Star I))
    (hHL : H ≤ d.starImage I c.L) (hH : H ≠ d.starImage I c.L)
    (hYH : d.starImage I d.Yplus ≤ H)
    (hSH : d.starImage I d.S ⊓ d.starImage I c.L ≤ H)
    (hn : d.starImage I d.S ≤ normalizer (H : Set (d.Star I))) :
    H ≤ d.starImage I (d.M ⊓ c.L) := by
  have hint : (H ⊔ d.starImage I d.S) ⊓ d.starImage I c.L = H := by
    apply le_antisymm ?_ (le_inf le_sup_left hHL)
    intro x hx
    have hm : x ∈ (H : Set (d.Star I)) * d.starImage I d.S := by
      rw [← coe_mul_of_right_le_normalizer_left H (d.starImage I d.S) hn]
      exact hx.1
    obtain ⟨h, hh, s, hs, he⟩ := hm
    have hsL : s ∈ d.starImage I c.L := by
      have hhx := (d.starImage I c.L).mul_mem ((d.starImage I c.L).inv_mem (hHL hh)) hx.2
      rw [← he, inv_mul_cancel_left] at hhx
      exact hhx
    exact he ▸ H.mul_mem hh (hSH ⟨hs, hsL⟩)
  have hproper : H ⊔ d.starImage I d.S ≠ ⊤ := by
    intro ht
    rw [ht, top_inf_eq] at hint
    exact hH hint.symm
  have hYjoin : d.starImage I (d.Yplus ⊔ d.S) ≤ H ⊔ d.starImage I d.S := by
    change ((d.Yplus ⊔ d.S).subgroupOf I).map (d.starMap I) ≤ _
    rw [subgroupOf_sup (a.yplus_le_intersection.trans inf_le_right) a.sylow_le, Subgroup.map_sup]
    exact sup_le_sup hYH le_rfl
  rw [a.intersectionStar_eq_inf]
  exact le_inf hHL (le_sup_left.trans
    (proper_star_overgroup_le_intersection d a.minimal a.sylow a.sylow_eq _ hYjoin hproper))

/-- The S₃ shadow bounds three-subgroup orders even after passage to the
star quotient; a rank bound by itself would lose this information. -/
theorem star_three_subgroup_card_le_three (X : Subgroup (d.Star I))
    (hX : X ≤ d.starImage I (d.MI I)) (hp : IsPGroup 3 X) : Nat.card X ≤ 3 := by
  let f : d.MI I →* d.Star I := (d.starMap I).comp (inclusion inf_le_right)
  have hf : f.range = d.starImage I (d.MI I) := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  let X' := X.subgroupOf f.range
  have hX' : IsPGroup 3 X' := hp.comap_of_injective _ f.range.subtype_injective
  obtain ⟨Q, hXQ⟩ := hX'.exists_le_sylow
  obtain ⟨P, hPQ⟩ := Sylow.mapSurjective_surjective f.rangeRestrict_surjective 3 Q
  have hcQ : Nat.card Q ≤ Nat.card P := by
    rw [← hPQ]
    exact Nat.card_le_card_of_surjective _
      (f.rangeRestrict.subgroupMap_surjective (P : Subgroup (d.MI I)))
  have hcX : Nat.card X = Nat.card X' :=
    (Nat.card_congr (subgroupOfEquivOfLe (hX.trans hf.ge)).toEquiv).symm
  rw [hcX]
  exact (Nat.card_le_card_of_injective (inclusion hXQ) (inclusion_injective hXQ)).trans
    (hcQ.trans (intersection_sylow_three_card_le_three d a.facts P))

/-- Restricting to the normal component preserves the full residual identity. -/
theorem componentIntersection_residual :
    (primeToResidual 3 (d.M ⊓ c.L : Subgroup G)).map (d.M ⊓ c.L).subtype = d.Yplus := by
  have hML : d.M ⊓ c.L ≤ d.MI I := le_inf inf_le_left (inf_le_right.trans (component_le c))
  let N := (d.M ⊓ c.L).subgroupOf (d.MI I)
  have hIL := (normal_subgroupOf_iff_le_normalizer (component_le c)).mp a.normal
  have hn : N.Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf (inf_le_left.trans d.M.le_normalizer) (inf_le_right.trans hIL)).trans
      inf_normalizer_le_normalizer_inf)
  let := hn
  have hres : primeToResidual 3 (d.MI I) ≤ N := by
    intro x hx
    have hy : (x : G) ∈ d.Yplus := a.facts.residual ▸ mem_map_of_mem _ hx
    exact ⟨x.property.1, a.contains hy⟩
  have he := congrArg (fun H : Subgroup (d.MI I) => H.map (d.MI I).subtype)
    (embedded_primeToResidual_eq_of_normal 3 N hres)
  rw [map_embedded_primeToResidual_of_hom, map_subgroupOf_eq_of_le hML,
    ← a.facts.residual] at he
  exact he

/-- The complete component-intersection residual identity in the actual quotient. -/
theorem componentIntersectionStar_residual :
    (primeToResidual 3 (d.starImage I (d.M ⊓ c.L))).map
      (d.starImage I (d.M ⊓ c.L)).subtype = d.starImage I d.Yplus := by
  rw [← starImage_embedded_residual d (inf_le_right.trans (component_le c)),
    a.componentIntersection_residual]

/-- The ambient intersection has exactly the same embedded residual image. -/
theorem intersectionStar_residual :
    (primeToResidual 3 (d.starImage I (d.MI I))).map
      (d.starImage I (d.MI I)).subtype = d.starImage I d.Yplus := by
  rw [← starImage_embedded_residual d (inf_le_right : d.MI I ≤ I),
    ← a.facts.residual]

/-- A centerless star component is self-centralizing. Its centralizer embeds
in the two-group quotient I*/L*, while I* has trivial two-core. -/
theorem componentStar_selfCentralizing
    (hz : center (d.starImage I c.L) = ⊥) :
    centralizer (d.starImage I c.L : Set (d.Star I)) = ⊥ := by
  let := a.componentStar_normal
  let C := centralizer (d.starImage I c.L : Set (d.Star I))
  let f := (QuotientGroup.mk' (d.starImage I c.L)).comp C.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxL : (x : d.Star I) ∈ d.starImage I c.L :=
      (QuotientGroup.eq_one_iff _).mp hx
    have hxz : (⟨x, hxL⟩ : d.starImage I c.L) ∈ center (d.starImage I c.L) := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (x.property y y.property)
    rw [hz] at hxz
    have he : (⟨x, hxL⟩ : d.starImage I c.L) = 1 := hxz
    exact Subtype.ext (congrArg (fun y : d.starImage I c.L => (y : d.Star I)) he)
  have hp : IsPGroup 2 (d.Star I ⧸ d.starImage I c.L) :=
    isPGroup_quotient_of_sup_eq_top _ _
      (a.starSylow_coe ▸ a.starSylow.isPGroup') a.star_generated
  have hC : C ≤ pCore 2 (d.Star I) := le_sSup ⟨inferInstance, hp.of_injective f hf⟩
  exact eq_bot_iff.mpr (hC.trans_eq
    (d.star_twoCore_eq_bot ⟨a.sylow, a.sylow_eq⟩ (d.Z_le_S a.module_le)))

/-- The component intersection has order divisible by three, since its residual
acts nontrivially on the component. -/
theorem componentIntersectionStar_three_dvd :
    3 ∣ Nat.card (d.starImage I (d.M ⊓ c.L)) := by
  by_contra h
  have hr : primeToResidual 3 (d.starImage I (d.M ⊓ c.L)) = ⊥ :=
    eq_bot_iff.mpr (primeToResidual_le ⊥ (by
      rw [index_bot]
      exact Nat.prime_three.coprime_iff_not_dvd.mpr h))
  have hy : d.starImage I d.Yplus = ⊥ := by
    rw [← a.componentIntersectionStar_residual, hr, Subgroup.map_bot]
  exact component_star_not_centralizing d c
    (a.yplus_le_intersection.trans inf_le_right) (hy ▸ bot_le)

end Input
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
