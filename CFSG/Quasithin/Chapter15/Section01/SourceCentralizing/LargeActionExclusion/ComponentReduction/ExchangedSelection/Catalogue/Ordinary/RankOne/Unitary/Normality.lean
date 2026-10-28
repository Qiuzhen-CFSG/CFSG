module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary
public import Theory.SpecificGroups.SU3.OrdinaryComponentRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal

/-!
# Relative normality of the ordinary unitary component

The actual PSU₃ model has odd-prime rank at least two. Two distinct
conjugate components would violate the source strongly quasithin bound
in G₁. Consequently L is normal in G₁, so the subsequent torus argument
uses the literal S-action without assuming ambient normality.
Source: Aschbacher--Smith 15.1.21, printed pp.1097--1098.
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

/-- Every ordinary unitary constructor is normal in the original G₁. -/
theorem PreExclusionSource.rankOne_unitary_normal
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSU d.L 3 (2^n)) :
    (d.L.subgroupOf d.G1).Normal := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  obtain ⟨r,hr,ho,hR⟩ :=
    BenderSuzuki.MatrixGroups.HermitianForm.OrdinaryBorel.exists_odd_rank_two J hn hF hconj
  apply normal_of_odd_rank (h := h) s hG hL hr ho
  rwa [primeRank_equiv r e]
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
