module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.ThreeRank
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Sylow
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource
public import Theory.GroupTheory.CComponent.RankTwoResidual
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.Alternating.PrimeRank

/-!
# The actual A₆ exclusion in the rank-two characteristic-two argument

The source Sylow subgroup meets the subnormal component L in a Sylow
subgroup. Since L is outside M, the actual intersection M ∩ L is proper.
Its image in L/O₂(L) remains proper because O₂(L) lies in that Sylow
intersection. The A₆ parabolic order bound then forces three-rank at most
one, contradicting the original three-rank of Y₊.

The rank-two C-component residual theorem supplies Y₊ ≤ L in this
A₆ model using its trivial center and outer group of order four. The final
original-input theorem also derives the earlier Sylow and theta conclusions. No common conjugate-pair
witness, centralizer-residual order, or extra block exclusion is assumed.
The remaining nonbinary cases of 15.3.18–22 require their distinct source
arguments.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.21,
printed p.1127; the containment is 15.3.17(2), printed p.1126.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
variable {G : Type*} [Group G] [Finite G]

/-- The original three-rank-two component cannot have A₆ as its two-core quotient
once the actual source containment Y₊ ≤ L of 15.3.17(2) is known. -/
theorem no_alternatingSix_quotient
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hθ : theta (d.MI I) = d.Yplus)
    (hrank : primeRank 3 d.Yplus = 2) (hYL : d.Yplus ≤ c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 6)) : False := by
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
  have hr := Theory.SpecificGroups.SymmetricSix.twoCoreQuotient_sylow_overgroup_three_rank_le_one
    e Q (d.M.subgroupOf c.L) hQM hM
  have hYM : d.Yplus ≤ d.M := hθ ▸ (theta_le (d.MI I)).trans inf_le_left
  have hbound : primeRank 3 d.Yplus ≤ primeRank 3 (d.M.subgroupOf c.L) := by
    rw [← primeRank_congr 3 (subgroupOfEquivOfLe hYL)]
    exact primeRank_mono 3 (subgroupOf_mono c.L hYM)
  omega

/-- The A₆-block clause of original 15.3.21, applied to its actual natural-module model. -/
theorem no_alternatingSix_block
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hθ : theta (d.MI I) = d.Yplus)
    (hrank : primeRank 3 d.Yplus = 2) (hYL : d.Yplus ≤ c.L)
    (hblock : ChapterC.IsAlternatingBlock c.L 6) : False := by
  obtain ⟨e⟩ := hblock.2.2.quotient_iso
  exact no_alternatingSix_quotient d c P hP hθ hrank hYL e

/-- In the A₆ case the original rank bound puts every local cubic generator
inside the component. This discharges the needed part of source 15.3.17. -/
theorem yplus_le_of_alternatingSix_quotient
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hθ : theta (d.MI I) = d.Yplus) (hrI : primeRank 3 I ≤ 2)
    (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 6)) :
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
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    apply mem_bot.mpr
    have he : f x ∈ center (alternatingGroup (Fin 6)) :=
      (centerCongr f ⟨x, hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact f.map_eq_one_iff.mp he
  have hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_congr 3 f,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 Nat.prime_three (by decide)]
  have ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) :=
    (IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card).of_injective
      (MulAut.outerCongr f).toMonoidHom (MulAut.outerCongr f).injective
  have hK : K = primeToResidual 3 I :=
    (LinearThree.Extension.SourceCases.component_in_overgroup d c).eq_primeToResidual_three_of_rank_outer_two
      hz hrK hrI ho
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

/-- Original-input A₆ branch of 15.3.21. The source Sylow and theta
premises are discharged; the remaining containment is precisely 15.3.17(2). -/
theorem source_15_3_21_alternatingSix_of_containment
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hrank : primeRank 3 d.Yplus = 2)
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (hblock : ChapterC.IsAlternatingBlock c.L 6) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  obtain ⟨P, hP⟩ := h11.sylow
  exact no_alternatingSix_block d c P hP h11.theta_eq.symm hrank hYL hblock

/-- The full A₆-block branch of original 15.3.21, with its local containment
and every preceding source premise discharged from the original setup. -/
theorem source_15_3_21_alternatingSix
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hrank : primeRank 3 d.Yplus = 2)
    (c : ComponentWitness d I)
    (hblock : ChapterC.IsAlternatingBlock c.L 6) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  obtain ⟨P, hP⟩ := h11.sylow
  obtain ⟨e⟩ := hblock.2.2.quotient_iso
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hYL := yplus_le_of_alternatingSix_quotient d c h11.theta_eq.symm hrI e
  exact no_alternatingSix_quotient d c P hP h11.theta_eq.symm hrank hYL e

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
