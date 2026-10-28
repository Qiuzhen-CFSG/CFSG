module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalApplicability
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.FixedPoints

/-!
# Earlier-source applicability for unitary noncentrality

The actual simple component quotient supplies the quasisimple quotient in
Hypothesis 12.2.3. Together with the original maximal faithful component,
this lets the structural 12.2.2 theorem control the same chosen module.
The natural action separately discharges the fixed-point condition of
13.3.13. No F.9 hypothesis or plane noncentrality is used.

Source: Aschbacher--Smith, 13.3.1--3 and 13.3.13, printed pp.884--885,890.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
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
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) :
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  have h12 := unitary_original_hypothesis1223 h hmax eL
  exact ⟨((structural G T L h12).2.2 V chosen).1,
    h12.source_chosen_normalizer_le structural
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) chosen⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
