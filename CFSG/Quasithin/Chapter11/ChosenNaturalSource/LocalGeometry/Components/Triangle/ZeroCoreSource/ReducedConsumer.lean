module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.NaturalBounds

/-!
# The original zero-core remainder and nonlinear common normal subgroup

Apply the marked field-four sieve to the canonical K₀ and original L₂.
The Sylow bounds exclude zero core for both nonlinear natural models;
the existing literal common-normal consumer then constructs I = K₀ ∨ L₂.
The linear-model G₂ comparison remains explicit in the remainder theorem.

Source: Aschbacher--Smith 11.1.2, printed pp.762--763. The broad reduced
DGS catalogue is the independent earlier-source input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
open ChapterF.Source ChapterF.Source.SuzukiContainment
open ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {L V : Subgroup G} (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

private theorem a5_of_psl_four {A : Type*} [Group A]
    (h : ClassicalGroup.IsPSL A 2 4) : Nonempty (A ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some⟩

variable {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The remaining zero-core branch has the original SL₃ natural marking and
an actual field-four G₂ comparison, with the original K₀, L₂ and whole S₀X.
This does not identify V₁ with the long-root group or exclude the remainder. -/
theorem original_zeroCore_remainder (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hm₀ : ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hz : pCore 2 (completion T X K₀ (f.Li 1)) = ⊥)
    (hdgs : Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives
      K₀ (f.Li 1) (commonTwo T X)) :
    (∃ m, c = Coordinates.sl3 m) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
        ∃ b : Bool, Nonempty (Iso (originalTriangle T X K₀ (f.Li 1)) (G2Native.amalgam F b)) := by
  obtain ⟨h,hb,_hp,_hg⟩ := original_hypothesis D S f hu hm₁ hm₂ hfour hX hK hLK
    hK₀ hK₀K hTK₀ hm₀ hk hp hz
  have he : locals K₀ (f.Li 1) = ![K₀,f.Li 1] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h hb
  have a : ∀ i, Nonempty ((![K₀,f.Li 1] i ⧸ pCore 2 (![K₀,f.Li 1] i)) ≃*
      alternatingGroup (Fin 5)) := by
    intro i
    fin_cases i
    · exact a5_of_psl_four hm₀
    · apply a5_of_psl_four
      simpa [hfour] using hm₂
  have hqt := S.source.simpleQTKE.quasithin.subgroup
    (generated ![K₀,f.Li 1] (commonTwo T X))
  have hc := original_fieldFour_comparison h hqt hb a hdgs
  exact ⟨linear_of_fieldFour_comparison D S hX hfour hc,
    g2_of_fieldFour_comparison D S c hX hfour hc⟩

/-- For either nonlinear natural model, the original common normal subgroup
exists conditionally only on the broad earlier DGS input. The same canonical
K₀ is retained and the existing literal I = K₀ ∨ L₂ consumer is instantiated. -/
theorem first_triangle_common_normal_of_nonlinear
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hnonlinear : ∀ m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3),
      c ≠ Coordinates.sl3 m)
    (hdgs : ∀ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T → K₀ < K →
      HypothesisF11 ![K₀,f.Li 1] (commonTwo T X) →
      Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives
        K₀ (f.Li 1) (commonTwo T X)) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ < K ∧ K₀ ≠ f.Li 0 ∧
      (∀ J : Subgroup G, J ∈ Chapter1.L G T → J ≤ K → J ≠ K → J ≠ f.Li 0 → J = K₀) ∧
      (T : Subgroup G) ≤ normalizer (K₀ : Set G) ∧ K₀ ∈ Chapter1.He G ∧
      f.Li 0 ⊔ K₀ = K ∧ ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4 ∧
      ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ (T : Subgroup G) ∧
          (T : Subgroup G) ≤ normalizer (Q : Set G) ∧
          K₀ ≤ normalizer (Q : Set G) ∧ f.Li 1 ≤ normalizer (Q : Set G) ∧
          Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
          (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T ∧ (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
          (solvableResidual ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
            ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 ∧
          (pResidual 2 ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
            ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 := by
  obtain ⟨K₀,h₀,hlt,hne,hu₀,hT,hHe,hgen,hm₀,hcases⟩ :=
    first_triangle_faithful_or_common_normal D S f hu hm₁ hm₂ hfour hfix hX hK hLK hk hp hcard hmove
  refine ⟨K₀,h₀,hlt,hne,hu₀,hT,hHe,hgen,hm₀,?_⟩
  rcases hcases with ⟨_hz,h,hb,_hp,_hg,_ht⟩ | hQ
  · have a : ∀ i, Nonempty ((![K₀,f.Li 1] i ⧸ pCore 2 (![K₀,f.Li 1] i)) ≃*
        alternatingGroup (Fin 5)) := by
      intro i
      fin_cases i
      · exact a5_of_psl_four hm₀
      · apply a5_of_psl_four
        simpa [hfour] using hm₂
    have hqt := S.source.simpleQTKE.quasithin.subgroup
      (generated ![K₀,f.Li 1] (commonTwo T X))
    have hc := original_fieldFour_comparison h hqt hb a (hdgs K₀ h₀ hlt h)
    obtain ⟨m,hm⟩ := linear_of_fieldFour_comparison D S (c := c) hX hfour hc
    exact (hnonlinear m hm).elim
  · exact hQ

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
