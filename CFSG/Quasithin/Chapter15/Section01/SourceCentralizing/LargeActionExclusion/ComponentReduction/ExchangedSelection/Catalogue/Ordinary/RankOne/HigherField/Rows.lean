module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.HigherField.Linear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.HigherField.Symplectic

/-!
# The remaining higher-field row after the simple model exclusions

The linear and symplectic source applications eliminate both simple
constructors. A trivial central two-core in the exceptional L₃(4)
quotient would give the already excluded simple linear model. Thus the
remaining row retains a nontrivial central cover, with no splitting claim.
This is a reduction of 15.1.20(3b), not its complete 15.1.21 exclusion.
Source: Aschbacher--Smith, printed pp.1096--1098.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Apply the simple model exclusions to the literal higher-field row. -/
theorem PreExclusionSource.higherField_after_simple_models
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : d.OrdinaryHigherField) (hpar : d.OrdinaryParabolic d.ML) :
    ClassicalGroup.IsPSL (d.L ⧸ pCore 2 d.L) 3 4 ∧ pCore 2 d.L ≠ ⊥ := by
  rcases hm with ⟨n,hn,hm | hm⟩ | hm
  · exact (s.false_of_linear_higherField (h := h) hG hM hJ hL hn hm hpar).elim
  · exact (s.false_of_symplectic_higherField (h := h) hG hM hJ hL hn hm hpar).elim
  · refine ⟨hm,?_⟩
    intro hbot
    let e : d.L ≃* (d.L ⧸ pCore 2 d.L) :=
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm
    exact s.false_of_linear_higherField (h := h) hG hM hJ hL (n:=2) (by decide)
      (by simpa using hm.of_mulEquiv e) hpar
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
