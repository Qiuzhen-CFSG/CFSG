module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.SymplecticFourParabolics
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.ParabolicDescent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.SolvableControl

/-!
# The original symplectic branch of 15.3.20

The original source hypotheses supply the C.2.7 input, the ordinary
component equality and the solvable supplement. The two invariant
parabolics then give proper outside overgroups, contradicting induction.
The final consumers take the literal block, star model, or marked
parabolic alternative; their quotient maps are the original source maps.

Source: Aschbacher–Smith 15.3.17 and 15.3.20, printed pp.1126–1128.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hproper : ∀ K : Subgroup G, K < I → K ∈ d.Hplus → ¬ HasCharacteristicTwo K)

include hG hempty hM hu hmany hI htwo hf hproper
/-- Source 15.3.20 for the actual symplectic-four core quotient. -/
theorem source_15_3_20_symplecticFour_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) : False := by
  have hin := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  have hθ := component_eq_theta_of_symplecticFour d c
    ((OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin
      3 Nat.prime_three (by decide)) hF e
  have hn : d.Yplus ⊔ d.S ≤ normalizer (c.L : Set G) :=
    hI.1.2.trans (LinearFourFive.normalizes_of_eq_theta hθ)
  have hAM : d.Yplus ⊔ d.S ≤ d.MI I := by
    refine sup_le ?_ (le_inf (inf_le_left.trans d.sylow_le)
      (le_sup_right.trans hI.1.2))
    rw [h11.theta_eq]
    exact theta_le _
  have hsol : Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) :=
    d.join_isSolvable_of_three_quotient hI h11.theta_eq.symm
      (ComponentIntersection.cubic_quotient_facts d.Yplus htwo.1).1
  obtain ⟨T,hT⟩ := LinearFourFive.sylow_intersection_of_eq_theta d h11.sylow hθ
  have hTA : (T : Subgroup c.L) ≤ (d.Yplus ⊔ d.S).subgroupOf c.L := by
    intro t ht
    have hm : (t : G) ∈ d.S ⊓ c.L := hT ▸ mem_map_of_mem c.L.subtype ht
    exact Subgroup.mem_sup_right hm.1
  obtain ⟨P,Q,hP,hQ,hgen,hnP,hnQ,hbase⟩ :=
    symplecticFour_original_parabolic_pair hin hn hAM hsol T hTA hF e
  exact source_15_3_20_of_generating_parabolics d hI h11.sylow hf c hproper
    P Q hP hQ hgen hnP hnQ hbase

/-- Literal block consumer for the symplectic alternative in C.2.7. -/
theorem source_15_3_20_symplecticFour
    (hb : ChapterC.IsSp4FourBlock c.L) : False := by
  obtain ⟨_,F,hField,hFinite,hF,ρ,⟨m⟩,_⟩ := hb
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (show Nat.card F = 2^2 by omega)
  exact source_15_3_20_symplecticFour_quotient
    hG d hempty hM hu hmany hI htwo hf c hproper hF m.quotientIso
/-- The symplectic-four star row of the actual C.2.7 actor is impossible. -/
theorem source_15_3_20_symplecticFour_star
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (e : Chapter1.RadicalExclusions.ModelReduction.starImage c.L d.R c.L ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F) : False := by
  have hin := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  exact source_15_3_20_symplecticFour_quotient hG d hempty hM hu hmany hI htwo hf c
    hproper hF (symplecticFour_core_equiv_of_star hin hF e)

/-- Direct consumer of the marked symplectic alternative in C.2.7(3). -/
theorem source_15_3_20_symplecticFour_parabolic
    (hp : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsSp4FourMaximalParabolic
      ((Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.starM c.L d.R (d.MI I)).subgroupOf
        (Chapter1.RadicalExclusions.ModelReduction.starImage c.L d.R c.L))) : False := by
  obtain ⟨F,hField,hFinite,hF,e,_⟩ := hp
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (show Nat.card F = 2^2 by omega)
  exact source_15_3_20_symplecticFour_star
    hG d hempty hM hu hmany hI htwo hf c hproper hF e

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
