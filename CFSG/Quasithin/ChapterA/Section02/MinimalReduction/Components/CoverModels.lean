module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.ComponentModels
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.TwoCore
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# The actual odd-center cover list for the component-product branch

Proper-section induction supplies the complete C model of each component's
central quotient. The independently proved covering calculations then show
that the component is simple or one of the actual three-covers. This uses
the raw model-by-model covering theorem, not the universal A.3.6 theorem
whose proof depends on Theorems A and C.

The only independent cover inputs are the precise odd-primary calculations
in `RemainingOddCoverInputs`; the source covering assembly discharges them.
No prime-core identity is needed for this component-list deduction.

Source: Aschbacher–Smith A.2.12(I), printed p.36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
open Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

private theorem not_fitting_eq_generalizedFitting {L : Type*} [Group L] [Finite L]
    [IsQuasisimple L] : fittingSubgroup L ≠ generalizedFitting L := by
  intro he
  have ht : fittingSubgroup L = ⊤ := he.trans generalizedFitting_eq_top_of_quasisimple
  let : Group.IsNilpotent (⊤ : Subgroup L) := ht ▸
    inferInstanceAs (Group.IsNilpotent (fittingSubgroup L))
  let : Group.IsNilpotent L :=
    Group.nilpotent_of_mulEquiv (topEquiv : (⊤ : Subgroup L) ≃* L)
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact Group.IsPerfect.not_isNilpotent L inferInstance

theorem CounterexampleToTheoremA.component_simple_or_threeCover
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    (hcovers : SQTKStructure.OrdinarySource.RemainingOddCoverInputs.{u})
    {C : Subgroup G} (hC : IsComponent G C) :
    IsSimpleGroup C ∨
      (Nonempty (center C ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel C) := by
  let := hC.2
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  have hmodels := component_centralQuotient_models_of_semisimple_not_quasisimple
    ih h.1 h.2.1 hsemi hn hC
  have hm := Section03.SourceComponents.sourceTheoremC_to_local
    (Group.IsPerfect.not_isMulCommutative (C ⧸ center C)) hmodels.2.2
  have hc := SQTKStructure.OrdinarySource.ordinary_conclusion hcovers
    (lemma_A_2_10 h ih.theoremA) C hC hm
  cases hc.1 with
  | simple _ hs _ => exact .inl hs
  | cover _ hz hm => exact .inr ⟨hz, hm⟩
  | natural hh => exact (not_fitting_eq_generalizedFitting hh.1.symm).elim
  | nilpotent hh => exact (not_fitting_eq_generalizedFitting hh.1.symm).elim

theorem CounterexampleToTheoremA.component_center_card_and_coverModel
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    (hcovers : SQTKStructure.OrdinarySource.RemainingOddCoverInputs.{u})
    {C : Subgroup G} (hC : IsComponent G C) :
    Nat.card (center C) = 1 ∨
      (Nat.card (center C) = 3 ∧ ThreeCoverModel C) := by
  let := hC.2
  rcases h.component_simple_or_threeCover ih hsemi hn hcovers hC with hs | ⟨⟨e⟩, hm⟩
  · let := hs
    have hz : center C = ⊥ :=
      (inferInstance : (center C).Normal).eq_bot_or_eq_top.resolve_right
        (fun ht => Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp ht))
    exact .inl (by rw [hz]; simp)
  · exact .inr ⟨by simpa using Nat.card_congr e.toEquiv, hm⟩

end CFSG.Quasithin.ChapterA.Section02
