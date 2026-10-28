module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.SourceCatalogue
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

/-!
# Comparing the two full B.4 source implications

For a faithful irreducible action of quadratic ratio at most two, the complete
B.4.5 implication gives either its full table or an FF-module. In the latter
case, offender attainment and replacement supply the actual best offender
required by the corrected full B.4.2 implication. The boundary is impossible
because its quadratic ratio is greater than two, including the J₂ case.

Both universal source implications remain explicit. The result assumes no
filtered list and preserves all the table rows and the corrected B.4.2
projective-line offender clause. The source owner must supply the faithful
chief action's SQTK, generalized-Fitting and irreducibility hypotheses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.2 and B.4.5, printed pp.86–87; application 13.5.21, printed p.924.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open ChapterB.SourceInduction.ProjectiveLine
open Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
universe u v
variable {E : Type u} [Group E] [Finite E]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- The complete B.4 action alternatives usable at quadratic ratio at most two.
The B.4.2 half uses the corrected projective-line convention. -/
def FullCatalogueAction (ρ : Representation (ZMod 2) E V) : Prop :=
  IrreducibleActionCase ρ (generalizedFitting E) (offenderSubgroup ρ) ∨
    TableB45 ρ (generalizedFitting E)

/-- The boundary cases of B.4.5, including J₂, contradict q ≤ 2 numerically.
Its FF case is passed to the corrected full B.4.2 with an actual best offender. -/
theorem fullCatalogue_of_sources
    (earlier42 : IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    (earlier45 : FullB45.{u,v} KnownSimple.IsKnownSimple)
    (ρ : Representation (ZMod 2) E V)
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hq : quadraticRatio ρ ≤ 2) : FullCatalogueAction ρ := by
  cases earlier45 E V ρ (h.with_quadratic_bound hq) with
  | ff hc =>
    obtain ⟨A, hA⟩ := h.exists_B42_of_cubic_le_one hc
    exact Or.inl (earlier42 E V ρ h.sqtk h.quasisimple h.faithful h.irreducible
      ⟨A, hA.bestOffender⟩)
  | table _ _ row => exact Or.inr row
  | boundary _ hbad _ => exact (not_lt_of_ge hq hbad).elim

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
