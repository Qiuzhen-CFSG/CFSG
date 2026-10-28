module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuCode
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.NativeM23
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.GM02.Generation
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.GM02.M23Spectrum
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads
public import Theory.Mathieu.SchurMultipliers.M23Kernel

/-!
# The original M23 source action is not an FF module

The literal perfect-cover theorem removes the center. The proved M22 small
degree bound and induced-head calculation establish the native M23 degree gap.
Three-conjugate generation then gives degree eleven for the original source
module, and native recognition marks it as the actual code or cocode. Their
checked no-FF calculations finish this branch of B.4.2 and K.4.
Source: Aschbacher--Smith printed pp.86 and 457--459; GM02 Proposition5.1.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu
open Representation.MathieuSmall.M23DegreeSpectrum
universe u v

/-- All cover, point-module and induced-head inputs of the source degree window are discharged. -/
theorem m23_degree_eleven : M23DegreeEleven.{u,v} := by
  apply m23DegreeEleven_of_gm02_inputs GM02.m23InvolutionGeneration
  apply GM02.m23SmallSpectrum_of_inputs
  · intro K _ _ _ he
    obtain ⟨e⟩ := he
    exact Sporadic.Mathieu.SchurMultipliers.m23_center_eq_bot_of_centralQuotientEquiv e
  · intro W _ _ _ σ hf hi hd
    let : σ.IsIrreducible := hi
    exact Representation.MathieuSmall.M22Recognition.DegreeThirty.finrank_le_twelve_of_le_thirty σ hf (by omega)
  · exact smallInducedHeads

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The literal M23 central quotient is impossible for the original source FF action. -/
theorem not_ff_m23 (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m23.Carrier)) :
    ¬ IsFFModule ρ := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := he
  have hs : ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu.SourceHypotheses ρ := {sqtk := h.sqtk, quasisimple := h.quasisimple, faithful := h.faithful, irreducible := h.irreducible, cubic_le_two := h.smallCubic}
  obtain ⟨_,_,hc | hd⟩ := source_m23_of_degree_and_small_recognition
    m23_degree_eleven m23SmallRecognition ρ hs e
  · exact not_ff_of_m23Code hc
  · exact not_ff_of_m23Cocode hd
end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
