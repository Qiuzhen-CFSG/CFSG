module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.Applicability
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalApplicability

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalUnitaryNoncentrality.Applicability`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original selected unitary component satisfies the genuine earlier
Hypothesis 12.2.3, with its literal quotient by the two-core. -/
theorem unitary_original_hypothesis1223 {T : Sylow 2 G} {L : Subgroup G}
    (h : Hypothesis1331 T L) (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived) :
    Hypothesis1223 KnownSimple.IsKnownSimple T L := by
  obtain ⟨hL,hf⟩ := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
    h.local_component
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup (L ⧸ pCore 2 L) := eL.isSimpleGroup
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect hL
  let : Group.IsPerfect (L ⧸ pCore 2 L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  have hz : center (L ⧸ pCore 2 L) = ⊥ :=
    (inferInstance : (center (L ⧸ pCore 2 L)).Normal).eq_bot_or_eq_top.resolve_right
      (fun hz => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz))
  have hq : IsQuasisimple (L ⧸ pCore 2 L) :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  exact h.hypothesis1311.hypothesis1223 ⟨hmax,hf⟩ hq

/-- Structural 12.2.2 and the proved full-catalogue A/C theorems give both
normalizer conditions needed to mark the original unitary flag. -/
theorem unitary_original_module_normalizers {T : Sylow 2 G} {L V : Subgroup G}
    (h : Hypothesis1331 T L) (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  have h12 := unitary_original_hypothesis1223 h hmax eL
  exact ⟨((structural L h12).2.2 V chosen).1,
    h12.source_chosen_normalizer_le_at structural
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) chosen⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
