module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Suzuki.Rows
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.MarkedSylow
public import Theory.SpecificGroups.Suzuki.CentralCoverSylowCenter

/-!
# Complete exclusion of the ordinary Suzuki constructors

In a nontrivial Sz(8) central cover the Sylow center is the covering center.
The original central involution induces a nontrivial involutory pointwise
Sylow fixer, contradicting the actual cover geometry. Together with the
simple Suzuki proof this removes both Suzuki constructors from the literal
rank-one row. No component-normalizing or splitting premise is retained.
The linear and unitary exclusions remain with the same rank-one owner.
Source: Aschbacher--Smith 15.1.20--21, pp.1095--1098, using I.2.2(4).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The marked involution excludes nontrivial central covers, without normality of L. -/
theorem PreExclusionSource.false_of_suzuki_nontrivial_cover
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)
    (hne : pCore 2 d.L ≠ ⊥) : False := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let ec := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  obtain ⟨P,_,α,hα,hαne,hfix⟩ := s.exists_nontrivial_sylow_fixer (h := h) hG hM hu hL
  exact hαne (BenderSuzuki.MatrixGroups.suzuki_eight_cover_sylow_fixer ec
    (s.ordinary hL).center_two ((s.ordinary hL).center_eq.symm ▸ hne) P α hα hfix)

/-- The entire exceptional quotient constructor is impossible, preserving its Borel clause. -/
theorem PreExclusionSource.false_of_suzuki_eight_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)
    (hB : d.ML = d.ordinaryBorel) : False := by
  by_cases hz : pCore 2 d.L = ⊥
  · let q : d.L ≃* (d.L ⧸ pCore 2 d.L) :=
      ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm
    exact s.false_of_suzuki_simple (h := h) hG hM hJ hL (by decide) (q.trans e) hB
  · exact s.false_of_suzuki_nontrivial_cover (h := h) hG hM hu hL e hz

/-- Only the actual linear and unitary models remain in the literal rank-one row. -/
theorem PreExclusionSource.rankOne_after_all_suzuki
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hmodel : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (hB : d.ML = d.ordinaryBorel) :
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL d.L 2 (2^f)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSU d.L 3 (2^f)) := by
  rcases s.rankOne_after_suzuki (h := h) hG hM hJ hL hmodel hB with hm | hm | ⟨⟨e⟩,_,hne⟩
  · exact Or.inl hm
  · exact Or.inr hm
  · exact (s.false_of_suzuki_nontrivial_cover (h := h) hG hM hu hL e hne).elim

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
