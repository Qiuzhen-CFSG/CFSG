module

public import CFSG.Quasithin.Chapter7.Section01To05.IndexTwoSpan
public import CFSG.Quasithin.Chapter7.Section01To05.WeakClosure

/-!
# The exact subgroup family in Lemma 7.5.3

The source generates W from C_V(B), where C_A(V) ≤ B ≤ A and
|B : C_A(V)| = 2. The inverse-image bridge identifies this literal family
with the element fixed-space span for the original induced automizer.
The equality case of E.3.31 then proves the span bounds without using
w < s. Centralizer rigidity is needed only for the additional identity
C_V(A) = C_V(Vᵍ) and for the displayed reverse quotient in 7.5.3.

The earlier global inequality w < s remains explicit in the full lemma;
its source producer is 7.3.4. This module is independent of the deferred
binary natural-plus-dual rank theorem 7.7.1.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 7.5.3, printed p.700, and E.3.28–31, printed pp.237–238.
-/

public section
namespace CFSG.Quasithin.Chapter7
open Subgroup Representation.BinaryOffender ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}

/-- The actual offender and the book's full inverse-image family give the
same subgroup W inside the original ambient group. -/
theorem offenderFixedSpan_eq_sourceFixedSpan (g : G) :
    offenderFixedSpan V g = sourceFixedSpan V (offenderNormalizer V g) := by
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 (offenderNormalizer V g) :=
    offender_elementary_of_le (show offenderNormalizer V g ≤
      V.map (MulAut.conj g).toMonoidHom from inf_le_left)
  exact ambientSubmodule_fixedSpaceSpan_eq_sourceFixedSpan V _ inf_le_right

/-- The equality-case span conclusions require no lower bound on s.
This is the exact portion of 7.5.3 used by the M₂₃ code contradiction. -/
theorem source_offender_span_bounds
    (hT : HypothesisE322 V T) (hFF : ¬ IsFFModule (automizerRepresentation V))
    {g : G} (hg : IsWOffenderAt V T g)
    (heq : globalR V = globalW V T + (primeRank 2 (Automizer V) : ℕ∞)) :
    let A := offenderNormalizer V g
    let W := sourceFixedSpan V A
    rank (inducedAutomizer V A) = primeRank 2 (Automizer V) ∧
      W ≤ V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
      globalW V T ≤ (subgroupCorank V W : ℕ∞) := by
  dsimp only
  let I := inducedAutomizer V (offenderNormalizer V g)
  let _ : IsElementaryAbelian 2 I := offender_inducedAutomizer_elementary V g
  have h31 := lemma_E_3_31 hT (Or.inr hFF) hg heq
  have hpos : 0 < rank I := by
    change 0 < rank (inducedAutomizer V (offenderNormalizer V g))
    rw [h31.1.1]
    exact automizer_primeRank_pos_of_globalW_ne_top hT hg.globalW_ne_top
  have hcore := automizerDualCore_eq_fixedSpaceSpan V I hpos
  change automizerDualCore V I (rank I - 1) = offenderFixedSpan V g at hcore
  rw [offenderFixedSpan_eq_sourceFixedSpan] at hcore
  change _ ∧ _ at h31
  rw [hcore] at h31
  exact ⟨h31.1.1, h31.1.2.2, h31.2.1⟩

/-- All three clauses of 7.5.3 for the literal subgroup family.
The preceding 7.3.4 input w < s is kept separate from these deductions. -/
theorem lemma_7_5_3
    (hT : HypothesisE322 V T) (hFF : ¬ IsFFModule (automizerRepresentation V))
    {g : G} (hg : IsWOffenderAt V T g)
    (hs : globalW V T < globalS V) :
    let Vg := V.map (MulAut.conj g).toMonoidHom
    let A := offenderNormalizer V g
    let W := sourceFixedSpan V A
    let U := V ⊓ centralizer (A : Set G)
    (globalR V = globalW V T + (primeRank 2 (Automizer V) : ℕ∞) →
      rank (inducedAutomizer V A) = primeRank 2 (Automizer V) ∧
      globalR V = (subgroupCorank Vg (A ⊓ centralizer (V : Set G)) : ℕ∞) ∧
      W ≤ V ⊓ normalizer (Vg : Set G) ∧
      globalW V T ≤ (subgroupCorank V W : ℕ∞) ∧
      ((subgroupCorank V W : ℕ∞) = globalW V T →
        W = V ⊓ normalizer (Vg : Set G) ∧
        IsWOffender Vg (g • T : Sylow 2 G) W ∧
        subgroupCorank W U = primeRank 2 (Automizer V))) ∧
    globalR V - globalW V T ≤ (rank (inducedAutomizer V A) : ℕ∞) ∧
    U = V ⊓ centralizer (Vg : Set G) := by
  dsimp only
  refine ⟨?_, (lemma_E_3_28 hT (Or.inr hFF) hg).2.2.1,
    (offender_fixedSpaceFamily_of_lt_globalS hg hs).1⟩
  intro heq
  have h := offender_equality_conclusions hT hFF hg hs heq
  change _ ∧ _ at h
  rw [offenderFixedSpan_eq_sourceFixedSpan] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

end CFSG.Quasithin.Chapter7
