module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.Braids
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.CompletionExtension

/-!
# Compatible full Ree reconstruction from the canonical braid

The exact faithful completion maps now extend to a full binary Ree equivalence
once the canonical braid is established. Both endpoint ranges and their actual
common Borel are retained. This supplies the reconstruction half of F.4.8 for
the original J.4.7 objects. The source smallness argument already produces a
coherent geometric reflection pair; the remaining pointed local selection
must identify its canonical pair orbit before applying this interface.

Source: Aschbacher--Smith F.4.8 and F.4.15--17, pp.278 and281--283; J.4.7,
pp.442--445. The extension uses the checked Parrott presentation and actual
Borel conjugation, with no recognition or group-order certificate assumption.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Theory.GroupTheory
namespace Completion
variable {G : Type*} [Group G] (c : Completion G)

/-- The reconstructed equivalence, oriented from the actual source to the full model. -/
def canonicalEquiv (hbraid : Tits.ExceptionalParabolics.FullRee.CompletionPresentation.CanonicalBraid c) :
    G ≃* ReeF4.Model 0 :=
  (Tits.ExceptionalParabolics.FullRee.CompletionPresentation.fullEquiv c hbraid).symm

@[simp] theorem canonicalEquiv_left
    (hbraid : Tits.ExceptionalParabolics.FullRee.CompletionPresentation.CanonicalBraid c)
    (x : Tits.ExceptionalParabolics.FullRee.first) : canonicalEquiv c hbraid (c.left x) = x := by
  rw [← Tits.ExceptionalParabolics.FullRee.CompletionPresentation.fullEquiv_left c hbraid x]
  exact MulEquiv.symm_apply_apply _ _

@[simp] theorem canonicalEquiv_right
    (hbraid : Tits.ExceptionalParabolics.FullRee.CompletionPresentation.CanonicalBraid c)
    (x : Tits.ExceptionalParabolics.FullRee.second) : canonicalEquiv c hbraid (c.right x) = x := by
  rw [← Tits.ExceptionalParabolics.FullRee.CompletionPresentation.fullEquiv_right c hbraid x]
  exact MulEquiv.symm_apply_apply _ _

@[simp] theorem canonicalEquiv_middle
    (hbraid : Tits.ExceptionalParabolics.FullRee.CompletionPresentation.CanonicalBraid c)
    (x : Tits.ExceptionalParabolics.FullRee.B) : canonicalEquiv c hbraid (c.middle x) = x := by
  rw [← Tits.ExceptionalParabolics.FullRee.CompletionPresentation.fullEquiv_middle c hbraid x]
  exact MulEquiv.symm_apply_apply _ _

theorem canonicalEquiv_left_map
    (hbraid : Tits.ExceptionalParabolics.FullRee.CompletionPresentation.CanonicalBraid c) :
    c.left.range.map (canonicalEquiv c hbraid).toMonoidHom = Tits.ExceptionalParabolics.FullRee.first := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    change canonicalEquiv c hbraid (c.left z) ∈ _
    rw [canonicalEquiv_left]
    exact z.property
  · intro hx
    exact ⟨c.left ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, canonicalEquiv_left c hbraid ⟨x, hx⟩⟩

theorem canonicalEquiv_right_map
    (hbraid : Tits.ExceptionalParabolics.FullRee.CompletionPresentation.CanonicalBraid c) :
    c.right.range.map (canonicalEquiv c hbraid).toMonoidHom = Tits.ExceptionalParabolics.FullRee.second := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    change canonicalEquiv c hbraid (c.right z) ∈ _
    rw [canonicalEquiv_right]
    exact z.property
  · intro hx
    exact ⟨c.right ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, canonicalEquiv_right c hbraid ⟨x, hx⟩⟩

theorem canonicalEquiv_middle_map
    (hbraid : Tits.ExceptionalParabolics.FullRee.CompletionPresentation.CanonicalBraid c) :
    c.middle.range.map (canonicalEquiv c hbraid).toMonoidHom = Tits.ExceptionalParabolics.FullRee.B := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    change canonicalEquiv c hbraid (c.middle z) ∈ _
    rw [canonicalEquiv_middle]
    exact z.property
  · intro hx
    exact ⟨c.middle ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, canonicalEquiv_middle c hbraid ⟨x, hx⟩⟩

end Completion
variable {G : Type*} [Group G]

/-- Literal original-subgroup consumer, retaining all three marked ranges. -/
theorem ofSource_recognition_of_canonical_braid
    (P₁ T P₂ : Subgroup G) (h₁ : T ≤ P₁) (h₂ : T ≤ P₂) (hgen : P₁ ⊔ P₂ = ⊤)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₁ T P₂ h₁ h₂)
      Tits.ExceptionalParabolics.FullRee.amalgam)
    (hbraid : Tits.ExceptionalParabolics.FullRee.CompletionPresentation.CanonicalBraid
      (ofSource P₁ T P₂ h₁ h₂ hgen e)) :
    ∃ E : G ≃* ReeF4.Model 0,
      P₁.map E.toMonoidHom = Tits.ExceptionalParabolics.FullRee.first ∧
      T.map E.toMonoidHom = Tits.ExceptionalParabolics.FullRee.B ∧
      P₂.map E.toMonoidHom = Tits.ExceptionalParabolics.FullRee.second := by
  let c := ofSource P₁ T P₂ h₁ h₂ hgen e
  refine ⟨Completion.canonicalEquiv c hbraid, ?_, ?_, ?_⟩
  · simpa only [c, ofSource_left_range] using Completion.canonicalEquiv_left_map c hbraid
  · simpa only [c, ofSource_middle_range] using Completion.canonicalEquiv_middle_map c hbraid
  · simpa only [c, ofSource_right_range] using Completion.canonicalEquiv_right_map c hbraid

end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
