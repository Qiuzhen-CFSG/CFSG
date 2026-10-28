module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.PairControl

/-!
# The literal parabolic closure and the remaining source contracts

The original Sylow subgroup S remains Sylow in P₀=⟨P,S⟩, and P₀ inherits
SQTK from the marked centralizer. The remaining closure structure and
fixed-pair alternatives are stated separately so their proofs can be
assembled without changing the source parabolic family.

The residual alternative is a product inside the original P. No conclusion
about P is inferred merely from a block or a product in P₀.
Source: Aschbacher--Smith, 15.1.22(*), printed pp.1098--1099.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
open Section03 Section03.InitialSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The actual subgroup denoted P₀ in the printed proof. -/
@[expose] def parabolicClosure (d : CaseIComponentData T M Mc V) (P : Subgroup G) :
    Subgroup G := P ⊔ d.S

theorem IsSourceParabolic.closure_le_centralizer
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P) :
    d.parabolicClosure P ≤ d.G1 :=
  sup_le (hP.le_component.trans d.L_component.1) d.S_le_G1

/-- The original S is Sylow in P₀, with its original embedding. -/
theorem PreExclusionSource.parabolicClosure_sylow
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    {P : Subgroup G} (hP : d.IsSourceParabolic P) :
    Chapter1.IsSylowIn 2 d.S (d.parabolicClosure P) :=
  s.centralizer_sylow.restrict le_sup_right hP.closure_le_centralizer

/-- SQTK comes from the actual marked centralizer, without a model tag. -/
theorem IsSourceParabolic.closure_sqtk
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) :
    IsSQTK KnownSimple.IsKnownSimple (d.parabolicClosure P) := by
  let := h.elementary
  let : IsElementaryAbelian 2 d.Z1 :=
    IsElementaryAbelian.of_le (d.Z1_le_fixed.trans inf_le_left)
  have hs := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    (IsElementaryAbelian.isPGroup 2 d.Z1)
  exact ⟨hs.stronglyQuasithin.of_injective (inclusion hP.closure_le_centralizer)
      (inclusion_injective hP.closure_le_centralizer),
    hs.isKGroup.of_injective (inclusion hP.closure_le_centralizer)
      (inclusion_injective hP.closure_le_centralizer)⟩

/-- The three structural inputs still to be proved for the literal P₀.
No placement, pair alternative, or residual product is included. -/
structure ParabolicClosureStructure (H : Subgroup G) (R : Sylow 2 H) : Prop where
  minimal : IsMinimalParabolicOver R ⊤
  fitting : generalizedFitting H = pCore 2 H
  solvable : Group.IsSolvable H

/-- A genuine A₃ block moving the literal canonical module in the closure. -/
@[expose] def HasMovingAThreeBlock (H : Subgroup G) (R : Sylow 2 H) : Prop :=
  ∃ A : Subgroup H, ChapterC.IsBlock A ∧ ChapterC.IsAlternatingBlock A 3 ∧
      A = ⁅A,elementaryAbelianMaxJ (R : Subgroup H)⁆ ∧
      (ChapterC.blockU A).map A.subtype = ⁅normalClosure
        (omegaOneCenterAmbient (R : Subgroup H) : Set H),A⁆ ∧
      ⁅normalClosure (omegaOneCenterAmbient (R : Subgroup H) :
        Set H),A⁆ ≠ ⊥

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
