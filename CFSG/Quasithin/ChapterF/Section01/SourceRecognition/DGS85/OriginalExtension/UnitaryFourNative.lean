module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.NativeRestoration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ExtensionDiagram
public import CFSG.Quasithin.Chapter5.Section03UnitaryNativeLift.ExactLift

/-!
# Original unitary-four restoration in both orientations

Every automorphism of the reduced U₄(2ᵐ) amalgam extends to the genuine
projective carrier for m > 1. Thus the action of the whole original Borel
preserves the universal completion kernel. The native Sylow normalizer makes
both native parabolics self-normalizing, so descent and normal-supplement
gluing construct the two original endpoint maps into one type-preserving
automorphism extension. Their restrictions are the supplied reduced maps.

No collapse of the outer action is asserted: in particular m = 2 and the
degree-two unitary extension remain available to the source consumers.
Source: DGS, *Groups and Graphs* (1985), (15.2), pp.226–228;
Aschbacher–Smith F.1.12(I)(6), pp.263–264. Reduced recognition is explicit.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.UnitaryFourNative
open GreenBook.LieModels.UnitaryFour

def endpoint (m : ℕ) (hm : 1 ≤ m) (point : Bool) : Subgroup (ProjectiveGroup m hm) :=
  if point then pointParabolic m hm else planeParabolic m hm

theorem overlap_le_endpoint (m : ℕ) (hm : 1 ≤ m) (point : Bool) :
    overlap m hm ≤ endpoint m hm point := by
  cases point
  · exact map_mono inf_le_right
  · exact map_mono inf_le_left

def amalgam (m : ℕ) (hm : 1 ≤ m) (point : Bool) :
    RankTwoAmalgam (endpoint m hm point) (overlap m hm) (endpoint m hm (!point)) :=
  ofSubgroups _ _ _ (overlap_le_endpoint m hm point) (overlap_le_endpoint m hm (!point))

def model (m : ℕ) (hm : 1 ≤ m) (point : Bool) :
    FaithfulCompletion (amalgam m hm point) (G := ProjectiveGroup m hm) :=
  .ofSubgroups _ _ _ (overlap_le_endpoint m hm point) (overlap_le_endpoint m hm (!point)) (by
    cases point
    · change planeParabolic m hm ⊔ pointParabolic m hm = ⊤
      rw [sup_comm]
      exact GreenBook.LieModels.UnitaryFour.parabolics_generate m hm
    · exact GreenBook.LieModels.UnitaryFour.parabolics_generate m hm)

theorem model_left_range (m : ℕ) (hm : 1 ≤ m) (point : Bool) :
    (model m hm point).left.range = endpoint m hm point :=
  FaithfulCompletion.ofSubgroups_left_range ..
theorem model_right_range (m : ℕ) (hm : 1 ≤ m) (point : Bool) :
    (model m hm point).right.range = endpoint m hm (!point) :=
  FaithfulCompletion.ofSubgroups_right_range ..
theorem model_middle_range (m : ℕ) (hm : 1 ≤ m) (point : Bool) :
    (model m hm point).middle.range = overlap m hm :=
  FaithfulCompletion.ofSubgroups_middle_range ..

theorem model_overlap (m : ℕ) (hm : 1 ≤ m) (point : Bool) :
    (model m hm point).left.range ⊓ (model m hm point).right.range =
      (model m hm point).middle.range := by
  rw [model_left_range, model_right_range, model_middle_range]
  cases point
  · exact (inf_comm _ _).trans (exact_overlap m hm)
  · exact exact_overlap m hm

theorem native_lifts (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m) (point : Bool)
    (a : Iso (amalgam m hm point) (amalgam m hm point)) :
    ∃ f : ProjectiveGroup m hm →* ProjectiveGroup m hm,
      (∀ x, f ((model m hm point).left x) = (model m hm point).left (a.left x)) ∧
      (∀ x, f ((model m hm point).right x) = (model m hm point).right (a.right x)) := by
  cases point
  · obtain ⟨f,hl,hr⟩ := Chapter5.UnitaryNativeLift.Four.native_automorphism m hm hmgt a.reverse
    exact ⟨f.toMonoidHom,hr,hl⟩
  · obtain ⟨f,hl,hr⟩ := Chapter5.UnitaryNativeLift.Four.native_automorphism m hm hmgt a
    exact ⟨f.toMonoidHom,hl,hr⟩

theorem endpoint_normalizer (m : ℕ) (hm : 1 ≤ m) (point : Bool) :
    normalizer (endpoint m hm point : Set (ProjectiveGroup m hm)) = endpoint m hm point := by
  let : Finite (ProjectiveGroup m hm) := Finite.of_surjective (projection m hm)
    (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project_surjective _ _)
  apply NativeRestoration.self_normalizing_of_sylow (projectiveSylow m hm)
  · exact (upperProjective_le_overlap m hm).trans (overlap_le_endpoint m hm point)
  · change normalizer (upperProjective m hm : Set (ProjectiveGroup m hm)) ≤ _
    rw [projectiveSylow_normalizer]
    exact overlap_le_endpoint m hm point

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (e : Iso (reducedAmalgam L S) (amalgam m hm point))

abbrev reducedCompletion := (model m hm point).comapIso e

theorem reduced_preserved (hmgt : 1 < m) :
    PreservesCompletionKernel h (reducedCompletion m hm point e) :=
  NativeRestoration.preserves_of_native_lifts (reducedOverlapAction h) e (model m hm point)
    (native_lifts m hm hmgt point)

theorem reduced_overlap :
    (reducedCompletion m hm point e).left.range ⊓ (reducedCompletion m hm point e).right.range =
      (reducedCompletion m hm point e).middle.range := by
  simp only [reducedCompletion, FaithfulCompletion.comapIso_left_range,
    FaithfulCompletion.comapIso_right_range, FaithfulCompletion.comapIso_middle_range]
  exact model_overlap m hm point

theorem reduced_normalizer (j : Fin 2) :
    normalizer ((completionEndpoint (reducedCompletion m hm point e) j).range :
      Set (ProjectiveGroup m hm)) = (completionEndpoint (reducedCompletion m hm point e) j).range := by
  fin_cases j
  · change normalizer ((reducedCompletion m hm point e).left.range : Set (ProjectiveGroup m hm)) =
      (reducedCompletion m hm point e).left.range
    rw [FaithfulCompletion.comapIso_left_range, model_left_range]
    exact endpoint_normalizer m hm point
  · change normalizer ((reducedCompletion m hm point e).right.range : Set (ProjectiveGroup m hm)) =
      (reducedCompletion m hm point e).right.range
    rw [FaithfulCompletion.comapIso_right_range, model_right_range]
    exact endpoint_normalizer m hm (!point)

/-- The full original pair in a genuine type-preserving extension of U₄(2ᵐ). -/
def extension (hmgt : 1 < m) : SourceCompletion.UnitaryNonbinary.SourceExtension
    (endpoint m hm point) (endpoint m hm (!point)) where
  carrier := (restoredSourceExtension h (reducedCompletion m hm point e)
    (reduced_preserved h m hm point e hmgt) (reduced_overlap m hm point e) (reduced_normalizer m hm point e)).carrier
  left := (restoredSourceExtension h (reducedCompletion m hm point e)
    (reduced_preserved h m hm point e hmgt) (reduced_overlap m hm point e) (reduced_normalizer m hm point e)).left
  right := (restoredSourceExtension h (reducedCompletion m hm point e)
    (reduced_preserved h m hm point e hmgt) (reduced_overlap m hm point e) (reduced_normalizer m hm point e)).right
  left_le := (restoredSourceExtension h (reducedCompletion m hm point e)
    (reduced_preserved h m hm point e hmgt) (reduced_overlap m hm point e) (reduced_normalizer m hm point e)).left_le
  right_le := (restoredSourceExtension h (reducedCompletion m hm point e)
    (reduced_preserved h m hm point e hmgt) (reduced_overlap m hm point e) (reduced_normalizer m hm point e)).right_le
  contains_inner := (restoredSourceExtension h (reducedCompletion m hm point e)
    (reduced_preserved h m hm point e hmgt) (reduced_overlap m hm point e) (reduced_normalizer m hm point e)).contains_inner
  preserves_types := by
    intro a ha
    have hh := (restoredSourceExtension h (reducedCompletion m hm point e)
      (reduced_preserved h m hm point e hmgt) (reduced_overlap m hm point e) (reduced_normalizer m hm point e)).preserves_types a ha
    simpa only [reducedCompletion, FaithfulCompletion.comapIso_left_range,
      FaithfulCompletion.comapIso_right_range, model_left_range, model_right_range] using hh
  left_inner := by
    have hh := (restoredSourceExtension h (reducedCompletion m hm point e)
      (reduced_preserved h m hm point e hmgt) (reduced_overlap m hm point e) (reduced_normalizer m hm point e)).left_inner
    simpa only [reducedCompletion, FaithfulCompletion.comapIso_left_range, model_left_range] using hh
  right_inner := by
    have hh := (restoredSourceExtension h (reducedCompletion m hm point e)
      (reduced_preserved h m hm point e hmgt) (reduced_overlap m hm point e) (reduced_normalizer m hm point e)).right_inner
    simpa only [reducedCompletion, FaithfulCompletion.comapIso_right_range, model_right_range] using hh
  factor := (restoredSourceExtension h (reducedCompletion m hm point e)
    (reduced_preserved h m hm point e hmgt) (reduced_overlap m hm point e) (reduced_normalizer m hm point e)).factor

/-- Restore every original Borel element and both endpoint inclusions, with
the supplied reduced markings unchanged on the reduced endpoints. -/
theorem exists_original_extension_iso (hmgt : 1 < m) :
    ∃ f : Iso (originalAmalgam L S) (extension h m hm point e hmgt).amalgam,
      (∀ b : commonBorel L S, (f.middle b : MulAut (ProjectiveGroup m hm)) =
        completionAction h (reducedCompletion m hm point e) (reduced_preserved h m hm point e hmgt) b) ∧
      (∀ x : parabolic L (SuzukiContainment.reducedSylow L S) 0,
        (f.left (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x) :
          MulAut (ProjectiveGroup m hm)) = MulAut.conj (e.left x).val) ∧
      (∀ x : parabolic L (SuzukiContainment.reducedSylow L S) 1,
        (f.right (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x) :
          MulAut (ProjectiveGroup m hm)) = MulAut.conj (e.right x).val) :=
  exists_original_sourceExtension_iso h (reducedCompletion m hm point e)
    (reduced_preserved h m hm point e hmgt) (reduced_overlap m hm point e) (reduced_normalizer m hm point e)

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.UnitaryFourNative
