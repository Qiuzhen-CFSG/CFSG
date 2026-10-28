module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalSource
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.Complete
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalSelected

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalSource`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory ChapterE OriginalPlaneCentralizers
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Atlas.G2.Natural.BinaryPointFlag
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original chosen natural module supplies its own flag before the
source contradiction; all local obligations have been proved. -/
theorem unitary_original_false_without_local_premises
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : OriginalFixedModule1332At T L)
    (five : OriginalAlternatingFiveModules1332At T L) : False := by
  obtain ⟨hTN,hNL⟩ := unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural
  obtain ⟨Z,B,U,hZB,hBU,hUV,hTZ,hTB,hTU,hZ,hB,hU⟩ :=
    exists_unitary_original_flag T L s.chosen.normalizes hTN hNL
      s.actor s.coordinates s.equivariant
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,U,Z,normalizer (Z : Set G)⟩
  exact unitary_original_false_of_source_inputs D s earlier hUV
    (hZB.trans (hBU.trans hUV)) hTZ hTU hZ hU B (hBU.trans hUV)
    hTB hB rfl h1332 fixed five

/-- The literal original PSU₃(3) quotient is excluded. The only retained
inputs are the preceding source theorems and the actual natural marking. -/
theorem unitary_original_quotient_exclusion_of_source_inputs
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : Hypothesis1331 T L) (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (e : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E : Additive V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he : ∀ (l : inducedAutomizer V L) v,
      E (automizerRepresentation V l v) = Atlas.G2.Natural.derivedAction F (e l) (E v))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : OriginalFixedModule1332At T L)
    (five : OriginalAlternatingFiveModules1332At T L) :
    ¬ ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 3 := by
  rintro ⟨K,_,_,J,hK,hJ,⟨eJ⟩⟩
  let s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V :=
    ⟨h,hmax,eJ.trans (J.projectiveEquivBinaryG2Derived hK hJ),chosen,structural,e,E,he⟩
  exact unitary_original_false_without_local_premises s earlier h1332 fixed five

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
