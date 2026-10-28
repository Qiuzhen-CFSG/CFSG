module

public import Theory.AtlasPort.LinearGroups.G2.BinaryProperSylowCore.ThreeRank
public import Theory.SpecificGroups.BinaryComponentResidual
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSix

/-!
# The actual binary G₂ exclusion in the rank-two argument

The rank-two C-component residual theorem puts the cubic subgroup Y₊ in L.
The source Sylow subgroup meets L in a Sylow subgroup, so M ∩ L is a proper
Sylow-two overgroup. Its two-core quotient image in the actual G₂(2)′ model
has three-rank at most one, contradicting the standing rank of Y₊.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.21,
printed p.1127. The actor is G₂(2)′, as in the existing C.1.30 block API.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
variable {G : Type*} [Group G] [Finite G]

/-- The literal binary derived G₂ quotient contradicts rank two in the
source component intersection once Y₊ is contained in L. -/
theorem no_binaryG2_quotient
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hθ : theta (d.MI I) = d.Yplus)
    (hrank : primeRank 3 d.Yplus = 2) (hYL : d.Yplus ≤ c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  obtain ⟨Q, hQ⟩ := LinearThree.Extension.SourceCases.component_sylow d c P hP
  have hQM : (Q : Subgroup c.L) ≤ d.M.subgroupOf c.L := by
    rw [hQ]
    exact fun _ hx => d.sylow_le hx.1
  have hM : d.M.subgroupOf c.L ≠ ⊤ := by
    intro hh
    apply c.outside
    intro x hx
    change (⟨x, hx⟩ : c.L) ∈ d.M.subgroupOf c.L
    rw [hh]
    exact mem_top _
  have hr := Atlas.G2.BinaryProperSylowCore.twoCoreQuotient_sylow_overgroup_three_rank_le_one
    e Q (d.M.subgroupOf c.L) hQM hM
  have hYM : d.Yplus ≤ d.M := hθ ▸ (theta_le (d.MI I)).trans inf_le_left
  have hbound : primeRank 3 d.Yplus ≤ primeRank 3 (d.M.subgroupOf c.L) := by
    rw [← primeRank_congr 3 (subgroupOfEquivOfLe hYL)]
    exact primeRank_mono 3 (subgroupOf_mono c.L hYM)
  omega

/-- The ordinary rank-two residual contains every cubic generator of Y₊. -/
theorem yplus_le_of_binaryG2_quotient
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hθ : theta (d.MI I) = d.Yplus) (hrI : primeRank 3 I ≤ 2)
    (e : (c.L ⧸ pCore 2 c.L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    d.Yplus ≤ c.L := by
  let K := c.L.subgroupOf I
  let a : K ≃* c.L := subgroupOfEquivOfLe (component_le c)
  let b : (K ⧸ pCore 2 K) ≃* (c.L ⧸ pCore 2 c.L) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let f := b.trans e
  let _ : Theory.GroupTheory.IsQuasisimple (c.L ⧸ pCore 2 c.L) :=
    c.core_quotient_quasisimple
  let _ : Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K) :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv b.symm
  have hfacts := Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv f
    Theory.SpecificGroups.BinaryComponentResidual.g2
  have hK : K = primeToResidual 3 I :=
    (LinearThree.Extension.SourceCases.component_in_overgroup d c).eq_primeToResidual_three_of_rank_outer_two
      hfacts.1 hfacts.2.1 hrI hfacts.2.2
  rw [← hθ]
  apply (closure_le _).mpr
  rintro x ⟨hx, hx3⟩
  have hres : (⟨x, hx.2⟩ : I) ∈ primeToResidual 3 I := by
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    change x ^ (3 ^ 1) = 1
    simpa only [pow_one, hx3] using pow_orderOf_eq_one x
  change (⟨x, hx.2⟩ : I) ∈ K
  rw [hK]
  exact hres

/-- The original-input binary derived G₂ quotient is excluded. -/
theorem source_15_3_21_binaryG2_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hrank : primeRank 3 d.Yplus = 2)
    (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  obtain ⟨P, hP⟩ := h11.sylow
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hYL := yplus_le_of_binaryG2_quotient d c h11.theta_eq.symm hrI e
  exact no_binaryG2_quotient d c P hP h11.theta_eq.symm hrank hYL e


/-- The binary G₂ block branch of original 15.3.21, with its actual
quotient model extracted from the C.1.30 natural-block conclusion. -/
theorem source_15_3_21_binaryG2
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hrank : primeRank 3 d.Yplus = 2)
    (c : ComponentWitness d I)
    (hblock : ChapterC.IsG2TwoBlock c.L) : False := by
  obtain ⟨e⟩ := hblock.quotient_iso
  exact source_15_3_21_binaryG2_quotient hG d hempty hM hu hmany hI hrank c e

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
