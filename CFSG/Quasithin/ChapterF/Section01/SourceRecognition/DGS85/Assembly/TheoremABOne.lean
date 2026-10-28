module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneOriginalRestoration

/-!
# The original noncommuting b=1 branch of DGS Theorem A

The marked restoration theorem gives the actual original inclusion diagram:
a binary PSL₃ or full Sp₄ pair, or a nonbinary type-preserving automorphism
extension of either native pair. The whole original Borel is retained in each
isomorphism. Applying the model completions also gives a finite faithful
completion with the exact full overlap, without asserting that the original
ambient group is finite or isomorphic to that completion.

The only inputs are F.1.11, a reduced critical pair, its noncommuting centers
and b=1. The other critical branches belong to the remaining assembly.
Source: DGS, *Groups and Graphs* (1985), Theorem A(a), pp.99–100;
Chapter 15, especially (15.1)–(15.2), pp.225–228.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
open Reduction OriginalExtension SourceCompletion.UnitaryNonbinary BOneOriginalRestoration
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The general original Theorem A(a) alternatives for noncommuting b=1.
The nonbinary rows retain their full outer extension, and both orientations
are available. Every comparison includes the whole original Borel. -/
theorem original_theorem_A_bOne
    (h : HypothesisF11 L S) {v w : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (m : ℕ), 0 < m ∧ Nat.card F = 2^m ∧
      ((∃ point : Bool,
          (m = 1 ∧ Nonempty (Iso (originalAmalgam L S) (LinearNative.amalgam F point))) ∨
          (1 < m ∧ ∃ E : SourceExtension (Matrix.PSL3.SmallCompletion.parabolic F point)
              (Matrix.PSL3.SmallCompletion.parabolic F (!point)),
            Nonempty (Iso (originalAmalgam L S) E.amalgam))) ∨
       (∃ point : Bool,
          (m = 1 ∧ Nonempty (Iso (originalAmalgam L S) (SymplecticNative.amalgam F point))) ∨
          (1 < m ∧ ∃ E : SourceExtension (SymplecticNative.endpoint F point)
              (SymplecticNative.endpoint F (!point)),
            Nonempty (Iso (originalAmalgam L S) E.amalgam)))) := by
  obtain ⟨F,_,_,_,m,hm,hF,he⟩ := small_original_comparison_of_critical_bOne h hc hne hb
  refine ⟨F,inferInstance,inferInstance,inferInstance,m,hm,hF,?_⟩
  rcases he with ⟨point,e,hr⟩ | ⟨point,e,hr⟩
  · left
    refine ⟨point,?_⟩
    rcases hr with ⟨hbin,⟨f,_⟩⟩ | ⟨hlarge,⟨E,f,_⟩⟩
    · exact Or.inl ⟨hbin,⟨f⟩⟩
    · exact Or.inr ⟨hlarge,E,⟨f⟩⟩
  · right
    refine ⟨point,?_⟩
    rcases hr with ⟨hbin,⟨f,_⟩⟩ | ⟨hlarge,⟨E,f,_⟩⟩
    · exact Or.inl ⟨hbin,⟨f⟩⟩
    · exact Or.inr ⟨hlarge,E,⟨f⟩⟩

private theorem completion_of_finite_model
    {A B C : Type*} [Group A] [Group B] [Group C] {α : RankTwoAmalgam A B C}
    {X : Type} [Group X] [Finite X] (d : FaithfulCompletion α (G := X))
    (ho : d.left.range ⊓ d.right.range = d.middle.range)
    (e : Iso (originalAmalgam L S) α) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y),
      ∃ c : FaithfulCompletion (originalAmalgam L S) (G := Y),
        c.left.range ⊓ c.right.range = c.middle.range := by
  refine ⟨X,inferInstance,inferInstance,d.comapIso e,?_⟩
  simpa only [FaithfulCompletion.comapIso_left_range,
    FaithfulCompletion.comapIso_right_range, FaithfulCompletion.comapIso_middle_range] using ho

/-- Apply the original branch to a finite faithful completion. Its endpoint
intersection is precisely the image of the whole original Borel. -/
theorem original_finite_completion_of_critical_bOne
    (h : HypothesisF11 L S) {v w : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X),
      ∃ c : FaithfulCompletion (originalAmalgam L S) (G := X),
        c.left.range ⊓ c.right.range = c.middle.range := by
  obtain ⟨F,_,_,_,m,_,_,he⟩ := original_theorem_A_bOne h hc hne hb
  rcases he with ⟨point,hr⟩ | ⟨point,hr⟩
  · rcases hr with ⟨_,⟨e⟩⟩ | ⟨_,E,⟨e⟩⟩
    · exact completion_of_finite_model (LinearNative.model F point) (LinearNative.model_overlap F point) e
    · have hg := (LinearNative.model F point).generated
      rw [LinearNative.model_left_range, LinearNative.model_right_range] at hg
      exact completion_of_finite_model (E.completion hg) (E.completion_overlap hg) e
  · rcases hr with ⟨_,⟨e⟩⟩ | ⟨_,E,⟨e⟩⟩
    · let d := FaithfulCompletion.ofSubgroups _ _ _
        (SymplecticNative.borel_le_endpoint F point) (SymplecticNative.borel_le_endpoint F (!point))
        (SymplecticNative.endpoints_generate F point)
      apply completion_of_finite_model d _ e
      simpa only [d, FaithfulCompletion.ofSubgroups_left_range,
        FaithfulCompletion.ofSubgroups_right_range, FaithfulCompletion.ofSubgroups_middle_range]
        using SymplecticNative.endpoints_inf F point
    · exact completion_of_finite_model (E.completion (SymplecticNative.endpoints_generate F point))
        (E.completion_overlap (SymplecticNative.endpoints_generate F point)) e

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
