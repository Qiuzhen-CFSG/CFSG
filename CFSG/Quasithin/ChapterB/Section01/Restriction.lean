module

public import Theory.Representation.BinaryOffender.Restriction

/-!
# B.1.5(1), (2), (6) and B.7.1: restriction of best offenders

This module proves the source statements for actual restricted actions.
`subspaceActionImage ρ W` is `Aut_G(W)`, the image of the stabilizer of `W`,
and `restrictedSubgroup ρ W A` is `Aut_A(W)`. Their tautological action on
`W` is faithful. The action kernel is the concrete subgroup
`subspaceKernel ρ W A = C_A(W)`; `subspaceQuotientEquiv` identifies its
relative quotient with `Aut_A(W)`. The nonzero commutator hypothesis is
expressed by the span of the differences `ρ a w - w`.

The imported restriction theorem compares dimensions for every
`C_A(W) ≤ B ≤ A`. Equality gives both equal original weights and
`C_V(B) = C_V(A) + C_W(B)`, so minimality and the kernel alternatives
follow. The lower-layer proof does not require ambient faithfulness;
the source-facing statements retain that hypothesis. Faithfulness on `W`
is stated by its pointwise condition. The appendix's older conditional
wrappers are preserved unchanged.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, printed p. 69 and pp. 118–119
(PDF pp. 80 and 129–130).
-/

public section

namespace CFSG.Quasithin.ChapterB
open Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)

/-- Source B.7.1(1), also B.1.5(1): the genuine restricted action image is a best offender. -/
theorem source_lemma_B_7_1_1 (_hfaithful : Function.Injective ρ) {A : Subgroup G}
    (hA : IsBestOffender ρ A)
    (hW : ∀ a ∈ A, ∀ w ∈ W, ρ a w ∈ W)
    (hmove : subspaceCommutator ρ W A ≠ ⊥) :
    IsBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) :=
  hA.restricted ρ W (le_subspaceStabilizer ρ W hW)
    (fun h => hmove ((subspaceCommutator_eq_bot_iff ρ W A).2 h))

/-- Source B.7.1(2): minimality descends, and equality of quotient rank and moved
codimension forces faithfulness on `W` and the fixed-space sum. -/
theorem source_lemma_B_7_1_2 (_hfaithful : Function.Injective ρ) {A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A)
    (hW : ∀ a ∈ A, ∀ w ∈ W, ρ a w ∈ W)
    (hmove : subspaceCommutator ρ W A ≠ ⊥) :
    IsMinimalBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) ∧
      (rank (restrictedSubgroup ρ W A) =
          fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) →
        (∀ a ∈ A, (∀ w ∈ W, ρ a w = w) → a = 1) ∧ W ⊔ fixedSpace ρ A = ⊤) := by
  have hstab := le_subspaceStabilizer ρ W hW
  have hn : ¬ W ≤ fixedSpace ρ A :=
    fun h => hmove ((subspaceCommutator_eq_bot_iff ρ W A).2 h)
  refine ⟨hA.restricted ρ W hstab hn, ?_⟩
  intro heq
  obtain ⟨hker, hspan⟩ := hA.faithful_span_of_image_rank_eq ρ W hstab hn heq
  exact ⟨(subspaceKernel_eq_bot_iff ρ W A).1 hker, hspan⟩

/-- Source B.7.1(3): the second branch uses the actual nontrivial pointwise kernel,
which is both a best offender and below `A` in the source's equal-weight order. -/
theorem source_lemma_B_7_1_3 (_hfaithful : Function.Injective ρ) {A : Subgroup G}
    (hA : IsBestOffender ρ A)
    (hW : ∀ a ∈ A, ∀ w ∈ W, ρ a w ∈ W)
    (_hmove : subspaceCommutator ρ W A ≠ ⊥)
    (heq : rank (restrictedSubgroup ρ W A) =
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)) :
    ((∀ a ∈ A, (∀ w ∈ W, ρ a w = w) → a = 1) ∧ W ⊔ fixedSpace ρ A = ⊤) ∨
      (subspaceKernel ρ W A ≠ ⊥ ∧ IsBestOffender ρ (subspaceKernel ρ W A) ∧
        EqualWeightLE ρ (subspaceKernel ρ W A) A) := by
  rcases hA.restriction_alternatives ρ W (le_subspaceStabilizer ρ W hW) heq with
    ⟨hker, hspan⟩ | h
  · exact Or.inl ⟨(subspaceKernel_eq_bot_iff ρ W A).1 hker, hspan⟩
  · exact Or.inr h

/-- Source B.1.5(1), with `Aut_G(W)` constructed from the stabilizer of `W`. -/
theorem source_lemma_B_1_5_1 (hfaithful : Function.Injective ρ) {A : Subgroup G}
    (hA : IsBestOffender ρ A)
    (hW : ∀ a ∈ A, ∀ w ∈ W, ρ a w ∈ W)
    (hmove : subspaceCommutator ρ W A ≠ ⊥) :
    IsBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) :=
  source_lemma_B_7_1_1 ρ W hfaithful hA hW hmove

/-- Source B.1.5(2), including the non-strong-offender clause. -/
theorem source_lemma_B_1_5_2 (_hfaithful : Function.Injective ρ) {A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A)
    (hW : ∀ a ∈ A, ∀ w ∈ W, ρ a w ∈ W)
    (hmove : subspaceCommutator ρ W A ≠ ⊥) :
    IsMinimalBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) ∧
      (¬ IsStrongOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) →
        (∀ a ∈ A, (∀ w ∈ W, ρ a w = w) → a = 1) ∧ W ⊔ fixedSpace ρ A = ⊤) := by
  have hstab := le_subspaceStabilizer ρ W hW
  have hn : ¬ W ≤ fixedSpace ρ A :=
    fun h => hmove ((subspaceCommutator_eq_bot_iff ρ W A).2 h)
  refine ⟨hA.restricted ρ W hstab hn, ?_⟩
  intro hns
  obtain ⟨hker, hspan⟩ := hA.faithful_span_of_not_strong ρ W hstab hn hns
  exact ⟨(subspaceKernel_eq_bot_iff ρ W A).1 hker, hspan⟩

/-- Source B.1.5(6): at equal rank and codimension, a nonfaithful restriction has
its actual kernel in `P(G,V)`. The stronger equal-weight assertion is B.7.1(3). -/
theorem source_lemma_B_1_5_6 (hfaithful : Function.Injective ρ) {A : Subgroup G}
    (hA : IsBestOffender ρ A)
    (hW : ∀ a ∈ A, ∀ w ∈ W, ρ a w ∈ W)
    (hmove : subspaceCommutator ρ W A ≠ ⊥)
    (heq : rank (restrictedSubgroup ρ W A) =
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)) :
    (∀ a ∈ A, (∀ w ∈ W, ρ a w = w) → a = 1) ∨ IsBestOffender ρ (subspaceKernel ρ W A) := by
  rcases source_lemma_B_7_1_3 ρ W hfaithful hA hW hmove heq with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2.1

end CFSG.Quasithin.ChapterB
