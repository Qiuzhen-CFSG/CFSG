module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.LinearNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ExtensionDiagram

/-!
# The full original linear extension diagram

The native linear lift preserves the completion kernel. The restored source
extension then contains both original endpoints and their entire common Borel.
Reindexing its native endpoint ranges gives the actual oriented PSL₃ parabolics;
the three reduced restrictions are the original marking followed by conjugation.
The carrier retains the type-preserving outer automorphisms.

Source: DGS, *Groups and Graphs* (1985), (15.2), printed pp.226–228.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.LinearNative
open SuzukiContainment SourceCompletion.UnitaryNonbinary
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original whole-Borel inclusion diagram in a native linear automorphism
extension, with all three reduced markings and either orientation retained. -/
theorem exists_original_extension_iso (h : HypothesisF11 L S) {m : ℕ} (hF : Nat.card F = 2^m) (hm : 1 < m)
    (point : Bool) (e : Iso (reducedAmalgam L S) (amalgam F point)) :
    ∃ E : SourceExtension (Matrix.PSL3.SmallCompletion.parabolic F point)
        (Matrix.PSL3.SmallCompletion.parabolic F (!point)),
      ∃ f : Iso (originalAmalgam L S) E.amalgam,
        (∀ x : parabolic L (reducedSylow L S) 0,
          (f.left (inclusion (reduced_parabolic_le h 0) x) : MulAut PSL(3,F)) =
            MulAut.conj (e.left x : PSL(3,F))) ∧
        (∀ x : parabolic L (reducedSylow L S) 1,
          (f.right (inclusion (reduced_parabolic_le h 1) x) : MulAut PSL(3,F)) =
            MulAut.conj (e.right x : PSL(3,F))) ∧
        (∀ b : commonBorel L (reducedSylow L S),
          (f.middle (inclusion (reduced_commonBorel_le h) b) : MulAut PSL(3,F)) =
            MulAut.conj (e.middle b : PSL(3,F))) := by
  let c := reducedCompletion F point e
  let hk := reduced_preserved F h point e hF hm
  have ho := reduced_overlap F point e
  have hN := reduced_normalizer F point e hF (show 0 < m by omega)
  obtain ⟨f,hb,hl,hr⟩ := exists_original_sourceExtension_iso h c hk ho hN
  have hb' (b : commonBorel L (reducedSylow L S)) :
      (f.middle (inclusion (reduced_commonBorel_le h) b) : MulAut PSL(3,F)) =
        MulAut.conj (e.middle b : PSL(3,F)) := by
    rw [hb, completionAction_reduced]
    exact congrArg MulAut.conj (congrArg Subtype.val (e.left_commutes b))
  have hleft : c.left.range = Matrix.PSL3.SmallCompletion.parabolic F point :=
    (FaithfulCompletion.comapIso_left_range (model F point) e).trans (model_left_range F point)
  have hright : c.right.range = Matrix.PSL3.SmallCompletion.parabolic F (!point) :=
    (FaithfulCompletion.comapIso_right_range (model F point) e).trans (model_right_range F point)
  let E₀ := restoredSourceExtension h c hk ho hN
  let E : SourceExtension (Matrix.PSL3.SmallCompletion.parabolic F point)
      (Matrix.PSL3.SmallCompletion.parabolic F (!point)) := {
    carrier := E₀.carrier
    left := E₀.left
    right := E₀.right
    left_le := E₀.left_le
    right_le := E₀.right_le
    contains_inner := E₀.contains_inner
    preserves_types := by rw [← hleft, ← hright]; exact E₀.preserves_types
    left_inner := by rw [← hleft]; exact E₀.left_inner
    right_inner := by rw [← hright]; exact E₀.right_inner
    factor := E₀.factor }
  exact ⟨E, f, hl, hr, hb'⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.LinearNative
