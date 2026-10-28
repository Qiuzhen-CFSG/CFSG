module
public import Theory.GroupTheory.CharacteristicSelfCentralizingAutomorphisms.Coprime
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits
/-!
# Order-five elements centralize alternating-three blocks

In a characteristic-two group of three-rank at most two, an A₃-block has
one or two conjugates. An element killed by five fixes the block. Its
induced automorphism fixes the characteristic four-group core, since five
is coprime to 4!, and the two-group restriction kernel then kills it.

This is the A₃-block calculation in Aschbacher--Smith 14.6.15, printed
p.1034. The actual embedded block, rather than a group-family label, is used.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]
/-- An automorphism of an A₃-block killed by five is trivial. -/
theorem IsAlternatingBlock.fifth_power_automorphism {X : Type*} [Group X]
    (h : IsAlternatingBlock X 3) (α : MulAut X) (hα : α ^ 5 = 1) : α = 1 := by
  let := h.2.1.finite
  have hq : Nat.card (X ⧸ pCore 2 X) = 3 := by
    obtain ⟨e⟩ := h.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hfour := h.2.1.core_card_four_of_quotient_three hq
  apply automorphism_eq_one_of_characteristic_card (pCore 2 X) pCore_isPGroup
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp h.2.1.fitting)
    (by decide : Nat.Coprime 5 2) _ α hα
  rw [hfour]
  decide

omit [Finite G] in
private theorem fifth_power_mem_of_index_two (B : Subgroup G) (hb : B.index = 2)
    {x : G} (hx : x ^ 5 = 1) : x ∈ B := by
  have hm := B.pow_mem (B.sq_mem_of_index_two hb x) 3
  rw [←pow_mul] at hm
  have he : x ^ (2 * 3) = x := by
    change x ^ (5+1) = x
    rw [pow_succ,hx,one_mul]
  rwa [he] at hm

/-- The orbit bound and literal block action force centralization. -/
theorem fifth_power_centralizes_alternatingThree
    (hf : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (X : Subgroup G) (hb : IsBlock X) (ha : IsAlternatingBlock X 3)
    {x : G} (hx : x ^ 5 = 1) : x ∈ centralizer (X : Set G) := by
  have hn : x ∈ normalizer (X : Set G) := by
    rcases RankOne.ChiProduct.normal_or_index_two hf hr
      (show IsChiBlockIn X from ⟨hb,Or.inr ⟨3,by decide,ha⟩⟩) with hn | hi
    · let := hn
      rw [normalizer_eq_top]
      exact mem_top x
    · exact fifth_power_mem_of_index_two _ hi hx
  have he : X.normalizerMonoidHom ⟨x,hn⟩ = 1 := by
    apply ha.fifth_power_automorphism
    rw [←map_pow]
    have hp : (⟨x,hn⟩ : normalizer (X : Set G)) ^ 5 = 1 := Subtype.ext hx
    rw [hp,map_one]
  have hk : (⟨x,hn⟩ : normalizer (X : Set G)) ∈ X.normalizerMonoidHom.ker := he
  rwa [normalizerMonoidHom_ker] at hk
end CFSG.Quasithin.ChapterC
