module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.LinearThreeParabolics
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.LinearThreeLarger.Sylow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.ParabolicDescent

/-!
# Original 15.3.20 for the larger natural SL3 blocks

The source selection makes the component normal and the supplement Yplus S
solvable. Its component Sylow marks two proper parabolics in the actual natural
SL3 quotient. The compatible action on the block module fixes each parabolic;
full preimages contain the supplement intersection and generate the component.
Proper-overgroup induction then places both in M, contradicting the selected
component outside M.

Source: Aschbacher–Smith, 15.3.20, printed p.1127.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Subgroup Theory.GroupTheory ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original 15.3.20 excludes the actual natural SL3 block over a field
larger than two, under induction only for proper outside overgroups. -/
theorem source_15_3_20_sl3
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)
    {n : ℕ} (hn : 1 < n) (hb : ChapterC.IsSL3EvenBlock c.L n) : False := by
  obtain ⟨hAL,hsol,S,hS⟩ := LinearThreeLarger.source_geometry
    hG d hempty hM hu hmany hI htwo hf c hn hb
  obtain ⟨_,_,F,_,_,hF,ρ,⟨m⟩,hρ⟩ := hb
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) := hsol
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ n by omega)
  have hSA : (S : Subgroup c.L).map c.L.subtype ≤ d.Yplus ⊔ d.S := by
    rw [hS, subgroupOf_map_subtype]
    exact inf_le_left.trans le_sup_right
  obtain ⟨P,Q,hP,hQ,hgen,hnP,hnQ,hbase⟩ := m.exists_invariant_SL3_parabolics
    (fun g v => (hρ g v).trans (Representation.specialLinearNatural_apply 3 g v.toAdd))
    hfour hAL S hSA
  exact source_15_3_20_of_generating_parabolics d hI
    (OutsideStructure.source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI).sylow
    hf c hproper P Q hP hQ hgen hnP hnQ hbase
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
