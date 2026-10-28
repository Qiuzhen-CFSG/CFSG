module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.AlternativesData
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.FourCentralizers

public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# A fixed involution for the cubic factor

The cubic factor normalizes the centralizer of the four-group. This
centralizer has order eight; its fixed subgroup has order congruent to
eight modulo three, so it contains a nonidentity element. Every element
of the centralizer squares to one. This proves the first fusion input
in Bender, *Finite groups with large subgroups* (1974), (4.1), p.225.
-/

open Subgroup MulAction

namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)
include h
/-- An order-three subgroup normalizing a four-group fixes an involution
in its ambient centralizer. -/
public theorem three_normalizing_four_fixes_involution [IsSimpleGroup G] (V X : Subgroup G) (hV : Nat.card V = 4)
    (hX : Nat.card X = 3) (hXV : X ≤ normalizer (V : Set G)) :
    ∃ t : G, t ∈ centralizer (V : Set G) ∧ orderOf t = 2 ∧
      X ≤ centralizer ({t} : Set G) := by
  let C := centralizer (V : Set G)
  let _ := conjMulDistribMulActionOfLeNormalizer X C
    (hXV.trans (normalizer_le_normalizer_centralizer V))
  let F := FixedPoints.subgroup X C
  have hp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hX)
  have hm := hp.card_modEq_card_fixedPoints C
  change Nat.card C % 3 = Nat.card F % 3 at hm
  have hc : Nat.card C = 8 := h.four_centralizer_card V hV
  rw [hc] at hm
  have hn : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by
    have hpos := Nat.card_pos (α := F)
    omega)
  let _ := hn
  obtain ⟨t, ht⟩ := exists_ne (1 : F)
  have ht1 : (t.val.val : G) ≠ 1 := by
    intro hh
    apply ht
    exact Subtype.ext (Subtype.ext hh)
  obtain ⟨S, hS⟩ := h.four_centralizer_is_sylow V hV
  have htS : t.val.val ∈ (S : Subgroup G) := hS ▸ t.val.property
  have ht2 : t.val.val ^ 2 = 1 := congrArg Subtype.val (h.any_sylow_square S ⟨_, htS⟩)
  refine ⟨t.val.val, t.val.property, orderOf_eq_prime ht2 ht1, ?_⟩
  intro u hu
  rw [mem_centralizer_singleton_iff]
  have hf := congrArg Subtype.val (t.property (⟨u, hu⟩ : X))
  change u * t.val.val * u⁻¹ = t.val.val at hf
  exact (mul_inv_eq_iff_eq_mul.mp hf)
end CFSG.Quasithin.Janko1CentralizerData
