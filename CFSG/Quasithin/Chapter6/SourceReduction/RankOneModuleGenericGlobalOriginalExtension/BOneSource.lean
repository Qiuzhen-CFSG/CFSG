module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.IntrinsicBOne.Recognition
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Catalogue

/-!
# Original generic comparisons from the noncommuting b=1 source branch

Intrinsic DGS recognition constructs a reduced linear or symplectic amalgam
from the actual critical pair. The original normalized-Borel transport puts
the same S inside the arbitrary selected perfect R and restores both endpoint
maps and the entire odd overlap. The original local quotient identifies the
field exponent with n, so the binary models are excluded before the strict
catalogue and both natural-block conclusions are returned.

This discharges recognition and restoration in this source branch. It does
not assert that every source pair has b=1 or noncommuting critical centers.
The exhaustive DGS alternatives and original uniqueness remain with their
existing producers, qt-dgs85-source-assembly and
qt-d-1222-rankone-global-uniqueness, for final generic assembly.

Source: DGS, *Groups and Graphs* (1985), (7.1), pp.126--127, (10.5),
pp.156--157, and Theorem D, p.224; Aschbacher--Smith F.1.12, pp.263--264,
and 5.2.6, pp.650--651 (`refs/groups-and-graphs.pdf`, `refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.OriginalExtension
open ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  {v w : Vertex (Reduction.reducedFamily ![L,R] (sourceS L H))}
  (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H)) v w)
  (hne : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H)) v,
    Z (Reduction.reducedFamily ![L,R] (sourceS L H)) w⁆ ≠ ⊥)
  (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
include d h hTH hp hc hne hb

/-- The actual noncommuting b=1 branch has a full original linear or
symplectic comparison at the original nonbinary exponent. The selected R
need not already be the whole residual of H. -/
theorem original_linear_or_symplectic_of_critical_bOne :
    sourceS L H ≤ R ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 2^n ∧
        ((Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
            (LinearThree.amalgam F)) ∨
          Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
            (LinearThree.amalgam F).reverse)) ∨
         (Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
            (SymplecticFour.amalgam F)) ∨
          Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
            (SymplecticFour.amalgam F).reverse))) := by
  obtain ⟨F,_,_,_,m,hm,hF,he⟩ :=
    Assembly.IntrinsicBOne.small_comparison_of_critical_bOne
      (d.hypothesisF11 h hTH) hc hne hb
  rcases he with ⟨point,⟨e⟩⟩ | ⟨point,⟨e⟩⟩
  · have f := d.originalLinearComparisonOfReduced h hTH hp F hm hF point e
    have he : Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (LinearThree.amalgam F)) ∨
        Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
          (LinearThree.amalgam F).reverse) := by
      cases point
      · exact Or.inl ⟨f⟩
      · exact Or.inr ⟨f⟩
    obtain ⟨hmn,hL,hR⟩ := d.linear_amalgam_blocks h hTH hp F hm hF he
    have hs := (linear_original_core_and_containment_of_reduced_iso d h hTH F
      (d.linear_reduced_parameter h hTH hp F hm hF point e) hF point e hp).2
    exact ⟨hs,hL,hR,F,inferInstance,inferInstance,inferInstance,
      by simpa only [hmn] using hF,Or.inl he⟩
  · obtain ⟨⟨f⟩,hmn,_,hL,hR⟩ :=
      symplectic_original_comparison_of_reduced_iso d h hTH hp F hm hF point e
    have he : Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (SymplecticFour.amalgam F)) ∨
        Nonempty (Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
          (SymplecticFour.amalgam F).reverse) := by
      cases point
      · exact Or.inr ⟨f⟩
      · exact Or.inl ⟨f⟩
    have hs := (symplectic_original_core_and_containment_of_reduced_iso
      d h hTH hp F hm hF point e).2
    exact ⟨hs,hL,hR,F,inferInstance,inferInstance,inferInstance,
      by simpa only [hmn] using hF,Or.inr he⟩

/-- Construct the catalogue entry from the source critical branch, with no
model marking, quotient recognition or original-extension premise. -/
theorem concreteComparison_of_critical_bOne :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  obtain ⟨_,_,_,F,_,_,_,hF,he⟩ :=
    d.original_linear_or_symplectic_of_critical_bOne h hTH hp hc hne hb
  rcases he with he | he
  · exact .linear F n (by have := h.exponent; omega) hF he
  · exact .symplectic F n (by have := h.exponent; omega) hF he

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
