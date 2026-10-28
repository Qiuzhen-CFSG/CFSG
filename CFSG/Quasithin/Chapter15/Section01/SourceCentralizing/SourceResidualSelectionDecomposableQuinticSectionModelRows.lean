module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionModelRestriction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Marked

/-!
# Marked B.5 rows for the actual strong seed actor

The central moved quotient uses the same actor group, and passing to it
cannot increase fixed codimension. The literal seed-image strong offender
therefore excludes every ratio-one row of the complete B.4.2 catalogue.
The remaining rows retain their action equivalences, field bounds, generated
subgroup equalities and exact quadratic ratios. No rank equality between an
original actor and its seed image is used.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

omit [Finite G] in
/-- Strength survives on the moved central section for the unchanged actor. -/
theorem strong_on_moved_section
    (σ : Representation (ZMod 2) G W) {A L : Subgroup G}
    (hA : IsStrongOffender σ A) (s : MovedSection σ L) :
    IsStrongOffender s.action A := by
  refine ⟨hA.1, ?_⟩
  have hq := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
  have hs := fixedCodim_subrepresentation_le σ s.space A
  change fixedCodim s.action A + _ ≤ _ at hq
  exact lt_of_le_of_lt ((Nat.le_add_right _ _).trans (hq.trans hs)) hA.2

/-- The five marked rows remaining after the original seed actor is strong.
The group and representation in every marking are the actual quotient action. -/
@[expose] def StrongPlaneActionRows (σ : Representation (ZMod 2) G W) (L : Subgroup G) : Prop :=
  (∃ F : BinaryField, F.degree ≤ 2 ∧ offenderSubgroup σ = L ∧
    Nonempty (ActionEquiv (σ.comp L.subtype) (linearNatural F 3)) ∧
    quadraticRatio σ = 1 / 2) ∨
  (∃ F : BinaryField, F.degree = 2 ∧ offenderSubgroup σ = L ∧
    Nonempty (ActionEquiv (σ.comp L.subtype) (binarySymplectic F)) ∧
    quadraticRatio σ = 2 / 3) ∨
  (Nonempty (MarkedActionEquiv σ (offenderSubgroup σ) L
      (symplecticNatural (k := ZMod 2) 2)
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) ∧
    quadraticRatio σ = 2 / 3) ∨
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ offenderSubgroup σ = L ∧
    Nonempty (ActionEquiv (σ.comp L.subtype) (linearNatural BinaryField.two n)) ∧
    quadraticRatio σ = 1 / (n - 1 : ℕ)) ∨
  (offenderSubgroup σ = ⊤ ∧
    Nonempty (MarkedActionEquiv σ (offenderSubgroup σ) L
      (BinaryPermutation.naturalRepresentation (Fin 8)) (alternatingGroup (Fin 8))) ∧
    quadraticRatio σ = 3 / 4)

/-- The complete marked source catalogue loses its ratio-one rows, using
strength of the actual actor and its original moved-plane bound. -/
theorem strong_plane_action_rows
    (σ : Representation (ZMod 2) G W) (hf : Function.Injective σ)
    {A L : Subgroup G} (hstrong : IsStrongOffender σ A)
    (hd : Module.finrank (ZMod 2) (moved σ A) ≤ 2)
    (hc : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase
      σ L (offenderSubgroup σ)) :
    StrongPlaneActionRows σ L := by
  obtain ⟨B, hBA, hbest, _⟩ := hstrong.exists_bestOffender σ
  have hBA' : moved σ B ≤ moved σ A := by
    apply Submodule.span_mono
    rintro v ⟨b, hb, w, hw, hv⟩
    exact ⟨b, hBA hb, w, hw, hv⟩
  have hdB := (Submodule.finrank_mono hBA').trans hd
  have hAH := hbest.le_offenderSubgroup σ
  have hn : quadraticRatio σ ≠ 1 := by
    intro he
    have ht := (isStrongFFModule_iff_quadraticRatio_lt_one σ).mp ⟨A, hstrong⟩
    rw [he] at ht
    exact (lt_irrefl _ ht)
  cases hc with
  | linearTwo _ _ _ _ hr => exact (hn hr).elim
  | linearThree F gen e hr =>
    exact Or.inl ⟨F, SmallMoved.model_field_degree_le_two F σ hf hbest.1.1
      (gen ▸ hAH) hdB (specialLinearNatural 3) e, gen, ⟨e⟩, hr⟩
  | symplectic F large gen e hr =>
    have hF := SmallMoved.model_field_degree_le_two F σ hf hbest.1.1
      (gen ▸ hAH) hdB (symplecticNatural 2) e
    exact Or.inr (Or.inl ⟨F, by omega, gen, ⟨e⟩, hr⟩)
  | symplecticTwo e hr => exact Or.inr (Or.inr (Or.inl ⟨⟨e⟩, hr⟩))
  | g2 _ _ _ _ _ hr => exact (hn hr).elim
  | g2Two _ _ hr => exact (hn hr).elim
  | symmetric _ _ _ _ hr => exact (hn hr).elim
  | alternatingSix _ _ _ hr => exact (hn hr).elim
  | alternatingSeven _ _ _ _ _ hr => exact (hn hr).elim
  | tripleSix _ _ hr => exact (hn hr).elim
  | binaryLinear n hd gen e hr =>
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hd, gen, ⟨e⟩, hr⟩)))
  | orthogonalSix _ _ _ _ hr => exact (hn hr).elim
  | symmetricEight ht e hr =>
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, ⟨e⟩, hr⟩)))
  | exteriorFive _ _ _ _ _ hr => exact (hn hr).elim

/-- Apply the sieve to the literal complete B.5 moved section. Strength of
its same actor is retained in the irreducible branch; no seed rank is inferred. -/
theorem strong_source_marked_of_plane
    (σ : Representation (ZMod 2) G W) {A L : Subgroup G}
    (hstrong : IsStrongOffender σ A)
    (hd : Module.finrank (ZMod 2) (moved σ A) ≤ 2)
    (s : MovedSection σ L)
    (hc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase σ L s) :
    (IsIrrPlus σ L s.space.toSubmodule ∧ Function.Injective s.action ∧
      IsIrreducible (s.action.comp L.subtype) ∧ IsStrongOffender s.action A ∧
      StrongPlaneActionRows s.action L) ∨
    ∃ n, (n = 4 ∨ n = 5) ∧
      IsLinearNatural (s.space.toRepresentation.comp L.subtype) BinaryField.two n := by
  have hA : IsOffender σ A := ⟨hstrong.1, hstrong.2.le⟩
  rcases SmallMoved.source_irreducible_or_binary_of_plane σ hA hd s hc with hi | hb
  · have hs := strong_on_moved_section σ hstrong s
    have hdim := (moved_finrank_quotient_le s.space.toRepresentation s.central A).trans
      ((moved_finrank_subrepresentation_le σ s.space A).trans hd)
    exact Or.inl ⟨hi.1, hi.2.1, hi.2.2.1, hs,
      strong_plane_action_rows s.action hi.2.1 hs hdim hi.2.2.2⟩
  · exact Or.inr hb

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
