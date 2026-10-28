module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BaumannNormalization.FixedWitness
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Baumann normalization of the alternating-three and alternating-five blocks

The A3 core and natural quotient both have order four, so the fixed
kernel is trivial. Projectivity gives the corresponding A5 result.
The two-group fixed-point congruence supplies a noncentral Thompson-fixed
vector, and the fixed-witness theorem prevents permutation to a commuting
block. Source: Aschbacher--Smith C.1.16(2) and C.5.4(1), pp.125--126,155.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BaumannNormalization
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem alternating_three_fixed_bot {L : Type*} [Group L]
    (h : IsAlternatingBlock L 3) : blockFixed L = ⊥ := by
  let := h.2.1.finite
  obtain ⟨e⟩ := h.2.2.quotient_iso
  have hq : Nat.card (L ⧸ pCore 2 L) = 3 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hU : Nat.card (blockU L) = 4 := by
    rw [←h.2.1.core_eq_blockU_of_quotient_three hq]
    exact h.2.1.core_card_four_of_quotient_three hq
  have hm : Nat.card (BlockModule L) = 4 := by
    simpa using h.module_card_odd (by decide : Odd 3)
  have hc := card_eq_card_quotient_mul_card_subgroup (blockFixed L)
  change Nat.card (blockU L) = Nat.card (BlockModule L) * Nat.card (blockFixed L) at hc
  rw [hU,hm] at hc
  exact Subgroup.card_eq_one.mp (by omega)

omit [Finite G] in
theorem ambient_module_fixed_bot (K : Subgroup G) (h : blockFixed K = ⊥) :
    (blockU K).map K.subtype ⊓ centralizer (K : Set G) = ⊥ := by
  apply bot_unique
  rintro u ⟨⟨v,hv,rfl⟩,hc⟩
  have hvf : (⟨v,hv⟩ : blockU K) ∈ blockFixed K := by
    change v ∈ center K
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hc k k.property)
  rw [h,mem_bot] at hvf
  exact congrArg (fun v : blockU K => ((v : K) : G)) hvf

theorem normalizes_of_short_fixed_bot {ι : Type*} (R : Subgroup G)
    (K : ι → Subgroup G)
    (hperm : ∀ g ∈ R, ∀ i, ∃ j, (K i).map (MulAut.conj g).toMonoidHom = K j)
    (hcomm : Pairwise fun i j => ⁅K i,K j⁆ = ⊥)
    (i : ι) (hshort : IsShort (K i)) (hR : IsPGroup 2 R)
    (hUR : (blockU (K i)).map (K i).subtype ≤ R)
    (hmoved : K i = ⁅K i,elementaryAbelianMaxJ R⁆)
    (hfixed : blockFixed (K i) = ⊥) :
    ChapterB.baumann R ≤ normalizer (K i) := by
  let U := (blockU (K i)).map (K i).subtype
  let : IsElementaryAbelian 2 (blockU (K i)) := hshort.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (K i).subtype
  apply normalizes_of_fixed_witness R K hperm hcomm i U hUR (map_subtype_le _)
  apply fixed_noncentral_of_trivial_center R U (K i) hR
  · exact fun hz => hshort.blockU_ne_bot
      ((map_eq_bot_iff_of_injective _ (K i).subtype_injective).mp hz)
  · exact (normalizes_of_moved R (K i) hmoved).trans
      (normalizer_le_normalizer_characteristic_image (K i) (blockU (K i)))
  · exact ambient_module_fixed_bot (K i) hfixed

theorem normalizes_alternating {ι : Type*} (R : Subgroup G)
    (K : ι → Subgroup G)
    (hperm : ∀ g ∈ R, ∀ i, ∃ j, (K i).map (MulAut.conj g).toMonoidHom = K j)
    (hcomm : Pairwise fun i j => ⁅K i,K j⁆ = ⊥)
    (i : ι) (hR : IsPGroup 2 R)
    (hUR : (blockU (K i)).map (K i).subtype ≤ R)
    (hmoved : K i = ⁅K i,elementaryAbelianMaxJ R⁆)
    (h : IsAlternatingBlock (K i) 3 ∨ IsAlternatingBlock (K i) 5) :
    ChapterB.baumann R ≤ normalizer (K i) := by
  rcases h with h | h
  · exact normalizes_of_short_fixed_bot R K hperm hcomm i h.2.1 hR hUR hmoved
      (alternating_three_fixed_bot h)
  · exact normalizes_of_short_fixed_bot R K hperm hcomm i h.2.1 hR hUR hmoved
      h.blockFixed_eq_bot
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BaumannNormalization
