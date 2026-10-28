module
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFivePairSplit

/-!
# Centralizers in a pair of commuting alternating-five blocks

If the two-core is the product of the two natural layers, its centralizer
of either block is exactly the other layer. The natural layer has no fixed
points under its own alternating-five block. If the ambient two-core is
self-centralizing, the two blocks consequently have trivial joint
centralizer. These identities remove extra central kernels from the two
symmetric-five factor extensions in the zero-center branch of 10.2.1.

Source: Aschbacher–Smith, C.1.13(c) and 10.2.1, pp.124–125 and 742–743.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G]

private theorem alternatingFive_layer_fixed_bot (A : Subgroup G)
    (ha : IsAlternatingBlock A 5) :
    (blockU A).map A.subtype ⊓ centralizer (A : Set G) = ⊥ := by
  apply bot_unique
  rintro x ⟨⟨a,haU,rfl⟩,hc⟩
  have haZ : a ∈ center A := by
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (hc b b.property)
  have hz : blockU A ⊓ center A = ⊥ := by
    rw [←blockFixed_map,ha.blockFixed_eq_bot,Subgroup.map_bot]
  have h1 : a = 1 := by
    have hm : a ∈ blockU A ⊓ center A := ⟨haU,haZ⟩
    rwa [hz,mem_bot] at hm
  exact congrArg A.subtype h1

/-- The kernel of the second block action on the paired two-core is the
first block's actual natural layer. -/
theorem alternatingFive_pair_core_inf_centralizer
    (A B : Subgroup G) (hb : IsAlternatingBlock B 5) (hc : ⁅A,B⁆ = ⊥)
    (hs : pCore 2 G = (blockU A).map A.subtype ⊔ (blockU B).map B.subtype) :
    pCore 2 G ⊓ centralizer (B : Set G) = (blockU A).map A.subtype := by
  let U := (blockU A).map A.subtype
  let W := (blockU B).map B.subtype
  have hUC : U ≤ centralizer (B : Set G) :=
    (map_subtype_le _).trans (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hWU : W ≤ normalizer (U : Set G) :=
    (le_centralizer_iff.mp (hUC.trans (centralizer_le (map_subtype_le _)))).trans
      (centralizer_le_normalizer _)
  apply le_antisymm ?_ (le_inf (hs ▸ le_sup_left) hUC)
  rintro x ⟨hxQ,hxC⟩
  have hprod : x ∈ (U : Set G) * (W : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left U W hWU]
    exact hs ▸ hxQ
  obtain ⟨u,hu,w,hw,he⟩ := hprod
  have hwC : w ∈ centralizer (B : Set G) := by
    have hwx : w = u⁻¹ * x := by rw [←he]; group
    rw [hwx]
    exact (centralizer (B : Set G)).mul_mem
      ((centralizer (B : Set G)).inv_mem (hUC hu)) hxC
  have hw1 : w = 1 := by
    have hm : w ∈ (blockU B).map B.subtype ⊓ centralizer (B : Set G) := ⟨hw,hwC⟩
    rwa [alternatingFive_layer_fixed_bot B hb,mem_bot] at hm
  have hux : u = x := by simpa only [hw1,mul_one] using he
  exact hux ▸ hu

/-- Both literal kernels of the paired block actions. -/
theorem alternatingFive_pair_core_centralizers
    (A B : Subgroup G) (ha : IsAlternatingBlock A 5) (hb : IsAlternatingBlock B 5)
    (hc : ⁅A,B⁆ = ⊥)
    (hs : pCore 2 G = (blockU A).map A.subtype ⊔ (blockU B).map B.subtype) :
    pCore 2 G ⊓ centralizer (B : Set G) = (blockU A).map A.subtype ∧
      pCore 2 G ⊓ centralizer (A : Set G) = (blockU B).map B.subtype := by
  refine ⟨alternatingFive_pair_core_inf_centralizer A B hb hc hs,?_⟩
  apply alternatingFive_pair_core_inf_centralizer B A ha
  · rwa [commutator_comm]
  · simpa only [sup_comm] using hs

/-- The joint block centralizer is trivial when the paired core is
self-centralizing. -/
theorem alternatingFive_pair_centralizer_eq_bot
    (A B : Subgroup G) (ha : IsAlternatingBlock A 5) (hb : IsAlternatingBlock B 5)
    (hc : ⁅A,B⁆ = ⊥)
    (hs : pCore 2 G = (blockU A).map A.subtype ⊔ (blockU B).map B.subtype)
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) = ⊥ := by
  have hQ : pCore 2 G ≤ A ⊔ B := by
    rw [hs]
    exact sup_le_sup (map_subtype_le _) (map_subtype_le _)
  have hCQ : centralizer ((A ⊔ B : Subgroup G) : Set G) ≤ pCore 2 G :=
    (centralizer_le hQ).trans hself
  have hCU : centralizer ((A ⊔ B : Subgroup G) : Set G) ≤ (blockU A).map A.subtype := by
    rw [←alternatingFive_pair_core_inf_centralizer A B hb hc hs]
    exact le_inf hCQ (centralizer_le (show B ≤ A ⊔ B from le_sup_right))
  apply bot_unique
  exact (le_inf hCU (centralizer_le (show A ≤ A ⊔ B from le_sup_left))).trans
    (alternatingFive_layer_fixed_bot A ha).le

end CFSG.Quasithin.ChapterC
