module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary
public import Theory.SpecificGroups.Classical.EvenRankTwoOddRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal

/-!
# Normality of the ordinary higher-field component

Every model in the higher-field row has odd-prime rank at least two.
This rank lifts across the retained central two-core. Distinct conjugate
components would then supply odd-prime rank at least four in G₁, contrary
to its source strongly quasithin bound. Thus L is normal in G₁, including
the L₃(4) central covers; no ambient normality is assumed.

This discharges the component-normality premise in the model Thompson
calculation for Aschbacher--Smith 15.1.21(i), pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem normal_of_odd_rank
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {r : ℕ} (hr : r.Prime) (ho : Odd r) (hR : 2 ≤ primeRank r d.L) :
    (d.L.subgroupOf d.G1).Normal := by
  let : Fact r.Prime := ⟨hr⟩
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  let e := subgroupOfEquivOfLe (show d.L ≤ d.G1 from d.L_component.1)
  have hZ : IsPGroup 2 (center d.L) := by
    rw [(s.ordinary hL).center_eq]
    exact pCore_isPGroup
  have hZ' : IsPGroup 2 (center (d.L.subgroupOf d.G1)) := hZ.of_equiv (centerCongr e.symm)
  obtain ⟨n,hn⟩ := hZ'.exists_card_eq
  have hc : Nat.Coprime r (Nat.card (center (d.L.subgroupOf d.G1))) := by
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  have hR' : 2 ≤ primeRank r (d.L.subgroupOf d.G1) := by
    rwa [primeRank_equiv r e]
  exact hL.normal_of_coprime_center_primeRank r hc (by
    have hh := hsq.stronglyQuasithin r hr ho
    omega)

/-- The entire higher-field row has relative component normality. -/
theorem PreExclusionSource.higherField_normal
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : d.OrdinaryHigherField) : (d.L.subgroupOf d.G1).Normal := by
  rcases hm with ⟨n,hn,hm | hm⟩ | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    obtain ⟨r,hr,ho,hR⟩ := Theory.SpecificGroups.Classical.EvenRankTwoOddRank.linear hn hF
    apply normal_of_odd_rank (h := h) s hG hL hr ho
    rwa [primeRank_equiv r e]
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    apply normal_of_odd_rank (h := h) s hG hL Nat.prime_three (by decide)
    rw [primeRank_equiv 3 e]
    exact Theory.SpecificGroups.Classical.EvenRankTwoOddRank.symplectic
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    obtain ⟨r,hr,ho,hR⟩ := Theory.SpecificGroups.Classical.EvenRankTwoOddRank.linear
      (n:=2) (by decide) (by simpa using hF)
    let : Fact r.Prime := ⟨hr⟩
    apply normal_of_odd_rank (h := h) s hG hL hr ho
    rw [← primeRank_quotient_eq_of_isTwoGroup r ho (pCore 2 d.L) pCore_isPGroup,
      primeRank_equiv r e]
    exact hR
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
