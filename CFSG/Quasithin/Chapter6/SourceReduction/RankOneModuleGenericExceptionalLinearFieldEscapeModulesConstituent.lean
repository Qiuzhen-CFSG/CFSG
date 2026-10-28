module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesAction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.PSL3FourExclusion
public import Theory.Representation.BinaryOffender.PerfectOrbitSection

/-!
# Constructing the residual orbit section in the cubic escape

The faithful G.2.2 span action and the actual normal PSL₃(4) image
supply the homogeneous Irr⁺ member required by A.1.42. Its Sylow orbit
span is fully moved by that same image. Passing to the literal central
quotient retains a faithful component action; the original span need
not be irreducible. The Chapter 12 application supplies all these
inputs from the Cartan escape's residual image.

Source: Aschbacher--Smith A.1.42 and 5.1.23, printed pp.32,645--646.
The small cubic bound and the D.3 orbit collapse remain to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
open ChapterG.Section02
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

/-- A.1.42 on the faithful span action, with a faithful literal orbit quotient. -/
theorem exists_residual_orbit_section
    (h : D.Hypothesis) (K P : Subgroup (Actor h)) [K.Normal]
    (hm : ClassicalGroup.IsPSL K 3 4) (hP : IsPGroup 2 P) :
    HasFaithfulHomogeneousOrbitSection (representation h) K P := by
  obtain ⟨hqs,hz,_⟩ := ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm
  let := hqs
  let : IsSimpleGroup (K ⧸ center K) := hqs.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hPK : P ≤ normalizer (K : Set (Actor h)) := by
    rw [normalizer_eq_top]
    exact le_top
  exact hasFaithfulHomogeneousOrbitSection_of_faithful (representation h)
    (representation_faithful h) K P ((nontrivial_iff_ne_bot K).mp inferInstance) hz hPK hP

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
