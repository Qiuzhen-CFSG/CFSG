module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.Complete
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalSelected

/-!
# The selected unitary exclusion from the original earlier inputs

Construct the Sylow-invariant flag in the chosen natural module, then apply
the completed geometric and odd-normalizer contradiction. The actual
projective unitary quotient is identified with the binary G₂ derived group
using the proved exceptional isomorphism. No rank, noncentrality, plane,
maximal-action, flag, residual-uniqueness or odd-normalizer premise survives.

The preceding Chapter12 structure/recognition and Chapter13 catalogue/module
inputs remain explicit. Their independent producers and final `qt-theorem-d`
assembly retain their discharge. This module preserves the earlier conditional
public APIs and supplies their completed local counterpart.
Source: Aschbacher--Smith, 13.3.16--20, pp.894--896.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
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
    (s : Context T L V)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (e : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E : Additive V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he : ∀ (l : inducedAutomizer V L) v,
      E (automizerRepresentation V l v) = Atlas.G2.Natural.derivedAction F (e l) (E v))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : OriginalFixedModule1332At T L)
    (five : OriginalAlternatingFiveModules1332At T L) :
    ¬ ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 3 := by
  rintro ⟨K,_,_,J,hK,hJ,⟨eJ⟩⟩
  let s : Context T L V :=
    ⟨h,hmax,eJ.trans (J.projectiveEquivBinaryG2Derived hK hJ),chosen,structural,e,E,he⟩
  exact unitary_original_false_without_local_premises s earlier h1332 fixed five

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
