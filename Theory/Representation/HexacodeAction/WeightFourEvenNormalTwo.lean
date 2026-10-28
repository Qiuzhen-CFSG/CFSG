module

public import Theory.Representation.HexacodeAction.WeightFourVectorCore
public import Theory.Representation.HexacodeAction.FullWeightFourNormalTwo
import Theory.GroupTheory.SylowKernelCore

/-!
# Identifying an actual even normal two-subgroup at a weight-four vector

The even hypothesis fixes the whole scalar point. The literal normal
two-subgroup alternatives then give order four in the same product marking.
Normality in the even vector stabilizer puts the subgroup in its two-core;
their common order makes them equal, independently of any chosen S4 marking.

Source: Aschbacher--Smith, 12.7.15(2--3), printed p.843.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open BinaryOffender Theory.SpecificGroups.SymmetricSix DuadCalculation

/-- Every nontrivial normalized even two-subgroup fixing this weight-four
vector is the actual even vector-stabilizer two-core. -/
theorem weightFour_even_normal_two_eq_core (v : hexacode)
    (hv : hammingNorm v.val = 4) (N : Subgroup HexAutomorphisms)
    (hN : N ≤ fullVectorStabilizer v) (hp : IsPGroup 2 N) (hne : N ≠ ⊥)
    (hn : (fullWeightVectorStabilizer v).map hexSign.ker.subtype ≤
      normalizer (N : Set HexAutomorphisms))
    (heven : N ≤ hexSign.ker) :
    N = ((fullWeightVectorStabilizer v).pCoreIn 2).map hexSign.ker.subtype := by
  let E := (fullWeightVectorStabilizer v).map hexSign.ker.subtype
  have hNE : N ≤ E := by
    intro g hg
    exact ⟨⟨g, heven hg⟩, hN hg, rfl⟩
  have hle : N ≤ E.pCoreIn 2 := le_pCoreIn_of_normalizes hp hNE hn
  have hcore : E.pCoreIn 2 =
      ((fullWeightVectorStabilizer v).pCoreIn 2).map hexSign.ker.subtype :=
    (map_pCoreIn_of_injective 2 _ _ hexSign.ker.subtype_injective).symm
  have hv0 : v ≠ 0 := by intro hh; simp [hh] at hv
  obtain ⟨e, _, _, _, _, hpoint⟩ := fullWeightFour_normal_two_cases v hv N hN hp hne hn
  have hB : (N.subgroupOf (fullVectorStabilizer v)).map e.toMonoidHom =
      (⊥ : Subgroup Two).prod core := by
    apply hpoint
    rw [scalar_point_kernel_eq_even_vector v hv0]
    exact le_inf hN heven
  have hcardN : Nat.card N = 4 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv,
      ← card_map_of_injective (f := e.toMonoidHom) e.injective, hB,
      Nat.card_congr ((⊥ : Subgroup Two).prodEquiv core).toEquiv,
      Nat.card_prod, card_bot, core_card, one_mul]
  have hcardCore : Nat.card (E.pCoreIn 2) = 4 := by
    let eS := weightFourVectorStabilizerEquiv v hv
    rw [hcore, card_map_of_injective hexSign.ker.subtype_injective,
      pCoreIn, card_map_of_injective (fullWeightVectorStabilizer v).subtype_injective,
      ← card_map_of_injective (f := eS.toMonoidHom) eS.injective,
      pCore_map_iso 2 eS, ← core_eq, core_card]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardN, hcardCore])).trans hcore

end Representation.Hexacode
