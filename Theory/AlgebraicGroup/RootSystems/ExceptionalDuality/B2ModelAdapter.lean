module

public import Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.Core

/-!
# Type B2 exceptional-duality model adapter

This module transports the finite `B₂` matrix and positive-root fingerprint
checks to an arbitrary finite reduced crystallographic real root pairing whose
chosen, numbered base has classified type `B` and rank two.  Its principal
result says that two positive root-duality permutations on such a pairing are
equal.

The proof first identifies the based pairing with the standard
`typeBRootPairing 2`.  The four positive standard roots are enumerated
explicitly.  Matrix rigidity fixes both dualities on the simple roots, while
Coxeter-product preservation gives the same two-entry fingerprint for their
images of every positive root.  The checked `typeB2PositiveCoeffs` fingerprint
injectivity then identifies those images.  Negative roots are handled through
the root-index negation involution.  This is the rank-two type-B adapter for the
exceptional duality used in the GLS3 graph-field automorphism classification.
The same four-row enumeration also proves that every model root has one of the
two directed root lengths.
-/

namespace Theory.AlgebraicGroup

open StandardRootSystem

private noncomputable def b2PositiveIndex : Fin 4 → TypeBRootIndex 2
  | ⟨0, _⟩ => typeBSimpleRootIndex 0 0
  | ⟨1, _⟩ => typeBSimpleRootIndex 0 1
  | ⟨2, _⟩ => .inr (0, false)
  | ⟨3, _⟩ => .inl ⟨⟨(0, 1), by decide⟩, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

private lemma b2PositiveIndex_isPos (i : Fin 4) :
    (typeBRootPairing_base 0).IsPos (b2PositiveIndex i) := by
  have h0 : (typeBRootPairing_base 0).IsPos (b2PositiveIndex 0) := by
    have hidx : b2PositiveIndex 0 =
        (typeBRootPairing_baseEquiv 0 0 : TypeBRootIndex 2) := by
      rw [typeBRootPairing_baseEquiv_val]
      rfl
    rw [hidx]
    exact (typeBRootPairing_base 0).isPos_of_mem_support
      (typeBRootPairing_baseEquiv 0 0).property
  have h1 : (typeBRootPairing_base 0).IsPos (b2PositiveIndex 1) := by
    have hidx : b2PositiveIndex 1 =
        (typeBRootPairing_baseEquiv 0 1 : TypeBRootIndex 2) := by
      rw [typeBRootPairing_baseEquiv_val]
      rfl
    rw [hidx]
    exact (typeBRootPairing_base 0).isPos_of_mem_support
      (typeBRootPairing_baseEquiv 0 1).property
  have h2 : (typeBRootPairing_base 0).IsPos (b2PositiveIndex 2) := by
    exact h0.add h1 (by
      apply Subtype.ext
      ext k
      fin_cases k <;>
        norm_num [b2PositiveIndex, typeBSimpleRootIndex, typeBRootPairing_root,
          typeBRootInSpan_val, typeBRootEmbedding, typeBRootVector,
          basisVector, Pi.single_apply])
  have h3 : (typeBRootPairing_base 0).IsPos (b2PositiveIndex 3) := by
    exact h2.add h1 (by
      apply Subtype.ext
      ext k
      fin_cases k <;>
        norm_num [b2PositiveIndex, typeBSimpleRootIndex, typeBRootPairing_root,
          typeBRootInSpan_val, typeBRootEmbedding, typeBRootVector,
          basisVector, Pi.single_apply])
  fin_cases i <;> assumption

private lemma b2Root_eq_positive_or_negative (r : TypeBRootIndex 2) :
    ∃ i : Fin 4,
      (typeBRootPairing 2).root r =
          (typeBRootPairing 2).root (b2PositiveIndex i) ∨
        (typeBRootPairing 2).root r =
          -(typeBRootPairing 2).root (b2PositiveIndex i) := by
  rcases r with r | r
  · rcases r with ⟨⟨⟨a, b⟩, hab⟩, s, t⟩
    have hs := s.property
    have ht := t.property
    change s.1 = -1 ∨ s.1 = 1 at hs
    change t.1 = -1 ∨ t.1 = 1 at ht
    rcases hs with hs | hs
    · rcases ht with ht | ht
      · refine ⟨3, Or.inr ?_⟩
        fin_cases a <;> fin_cases b <;> simp at hab
        apply Subtype.ext
        ext k
        fin_cases k <;>
          norm_num [b2PositiveIndex, typeBSimpleRootIndex, typeBRootPairing_root,
            typeBRootInSpan_val, typeBRootEmbedding, typeBRootVector,
            basisVector, Pi.single_apply, hs, ht]
      · refine ⟨0, Or.inr ?_⟩
        fin_cases a <;> fin_cases b <;> simp at hab
        apply Subtype.ext
        ext k
        fin_cases k <;>
          norm_num [b2PositiveIndex, typeBSimpleRootIndex, typeBRootPairing_root,
            typeBRootInSpan_val, typeBRootEmbedding, typeBRootVector,
            basisVector, Pi.single_apply, hs, ht]
    · rcases ht with ht | ht
      · refine ⟨0, Or.inl ?_⟩
        fin_cases a <;> fin_cases b <;> simp at hab
        apply Subtype.ext
        ext k
        fin_cases k <;>
          norm_num [b2PositiveIndex, typeBSimpleRootIndex, typeBRootPairing_root,
            typeBRootInSpan_val, typeBRootEmbedding, typeBRootVector,
            basisVector, Pi.single_apply, hs, ht]
      · refine ⟨3, Or.inl ?_⟩
        fin_cases a <;> fin_cases b <;> simp at hab
        apply Subtype.ext
        ext k
        fin_cases k <;>
          norm_num [b2PositiveIndex, typeBSimpleRootIndex, typeBRootPairing_root,
            typeBRootInSpan_val, typeBRootEmbedding, typeBRootVector,
            basisVector, Pi.single_apply, hs, ht]
  · rcases r with ⟨a, sign⟩
    fin_cases a <;> cases sign
    · refine ⟨2, Or.inl ?_⟩
      rfl
    · refine ⟨2, Or.inr ?_⟩
      apply Subtype.ext
      ext k
      fin_cases k <;>
        norm_num [b2PositiveIndex, typeBRootPairing_root, typeBRootInSpan_val,
          typeBRootEmbedding, typeBRootVector, basisVector, Pi.single_apply]
    · refine ⟨1, Or.inl ?_⟩
      rfl
    · refine ⟨1, Or.inr ?_⟩
      apply Subtype.ext
      ext k
      fin_cases k <;>
        norm_num [b2PositiveIndex, typeBSimpleRootIndex, typeBRootPairing_root,
          typeBRootInSpan_val, typeBRootEmbedding, typeBRootVector,
          basisVector, Pi.single_apply]

private lemma b2PositiveIndex_surjective
    (r : TypeBRootIndex 2) (hr : (typeBRootPairing_base 0).IsPos r) :
    ∃ i : Fin 4, r = b2PositiveIndex i := by
  let _ := (typeBRootPairing 2).indexNeg
  rcases b2Root_eq_positive_or_negative r with ⟨i, hi | hi⟩
  · exact ⟨i, (typeBRootPairing 2).root.injective hi⟩
  · have hir : r = -(b2PositiveIndex i) := by
      apply (typeBRootPairing 2).root.injective
      have hneg : (typeBRootPairing 2).root (-(b2PositiveIndex i)) =
          -(typeBRootPairing 2).root (b2PositiveIndex i) := by
        change (typeBRootPairing 2).root ((typeBRootPairing 2).reflectionPerm
          (b2PositiveIndex i) (b2PositiveIndex i)) = _
        rw [(typeBRootPairing 2).root_reflectionPerm,
          (typeBRootPairing 2).reflection_apply_self]
      exact hi.trans hneg.symm
    rw [hir, RootPairing.Base.IsPos.neg_iff_not] at hr
    exact (hr (b2PositiveIndex_isPos i)).elim

private def b2PositiveCoxeterFingerprint : Fin 4 → Fin 2 → ℤ
  | ⟨0, _⟩ => ![4, 2]
  | ⟨1, _⟩ => ![2, 4]
  | ⟨2, _⟩ => ![2, 0]
  | ⟨3, _⟩ => ![0, 2]

private def b2PositiveForwardPairing : Fin 4 → Fin 2 → ℤ
  | ⟨0, _⟩ => ![2, -2]
  | ⟨1, _⟩ => ![-1, 2]
  | ⟨2, _⟩ => ![1, 0]
  | ⟨3, _⟩ => ![0, 2]

private def b2PositiveReversePairing : Fin 4 → Fin 2 → ℤ
  | ⟨0, _⟩ => ![2, -1]
  | ⟨1, _⟩ => ![-2, 2]
  | ⟨2, _⟩ => ![2, 0]
  | ⟨3, _⟩ => ![0, 1]

private lemma b2PositiveIndex_forwardPairing (i : Fin 4) (k : Fin 2) :
    (typeBRootPairing 2).pairingIn ℤ (b2PositiveIndex i)
        (typeBSimpleRootIndex 0 k) = b2PositiveForwardPairing i k := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
  change algebraMap ℤ ℝ ((typeBRootPairing 2).pairingIn ℤ
    (b2PositiveIndex i) (typeBSimpleRootIndex 0 k)) =
      algebraMap ℤ ℝ (b2PositiveForwardPairing i k)
  rw [(typeBRootPairing 2).algebraMap_pairingIn]
  fin_cases i <;> fin_cases k <;>
    norm_num [b2PositiveIndex, b2PositiveForwardPairing,
      typeBSimpleRootIndex, typeBRootPairing_pairing, typeBRootEmbedding,
      typeBRootVector, dot, basisVector, Pi.single_apply, Fin.sum_univ_two]

private lemma b2PositiveIndex_reversePairing (i : Fin 4) (k : Fin 2) :
    (typeBRootPairing 2).pairingIn ℤ (typeBSimpleRootIndex 0 k)
        (b2PositiveIndex i) = b2PositiveReversePairing i k := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
  change algebraMap ℤ ℝ ((typeBRootPairing 2).pairingIn ℤ
    (typeBSimpleRootIndex 0 k) (b2PositiveIndex i)) =
      algebraMap ℤ ℝ (b2PositiveReversePairing i k)
  rw [(typeBRootPairing 2).algebraMap_pairingIn]
  fin_cases i <;> fin_cases k <;>
    norm_num [b2PositiveIndex, b2PositiveReversePairing,
      typeBSimpleRootIndex, typeBRootPairing_pairing, typeBRootEmbedding,
      typeBRootVector, dot, basisVector, Pi.single_apply, Fin.sum_univ_two]

private lemma b2Root_abs_pairings_with_simple (r : TypeBRootIndex 2) :
    ∃ i : Fin 4, ∀ k : Fin 2,
      |(typeBRootPairing 2).pairingIn ℤ r (typeBSimpleRootIndex 0 k)| =
          |b2PositiveForwardPairing i k| ∧
        |(typeBRootPairing 2).pairingIn ℤ (typeBSimpleRootIndex 0 k) r| =
          |b2PositiveReversePairing i k| := by
  let _ := (typeBRootPairing 2).indexNeg
  rcases b2Root_eq_positive_or_negative r with ⟨i, hi | hi⟩
  · have hir : r = b2PositiveIndex i :=
      (typeBRootPairing 2).root.injective hi
    subst r
    exact ⟨i, fun k => by
      rw [b2PositiveIndex_forwardPairing, b2PositiveIndex_reversePairing]
      exact ⟨rfl, rfl⟩⟩
  · have hir : r = -(b2PositiveIndex i) := by
      apply (typeBRootPairing 2).root.injective
      have hneg : (typeBRootPairing 2).root (-(b2PositiveIndex i)) =
          -(typeBRootPairing 2).root (b2PositiveIndex i) := by
        change (typeBRootPairing 2).root ((typeBRootPairing 2).reflectionPerm
          (b2PositiveIndex i) (b2PositiveIndex i)) = _
        rw [(typeBRootPairing 2).root_reflectionPerm,
          (typeBRootPairing 2).reflection_apply_self]
      exact hi.trans hneg.symm
    subst r
    refine ⟨i, fun k => ?_⟩
    change
      |(typeBRootPairing 2).pairingIn ℤ
          ((typeBRootPairing 2).reflectionPerm (b2PositiveIndex i)
            (b2PositiveIndex i)) (typeBSimpleRootIndex 0 k)| = _ ∧
        |(typeBRootPairing 2).pairingIn ℤ (typeBSimpleRootIndex 0 k)
          ((typeBRootPairing 2).reflectionPerm (b2PositiveIndex i)
            (b2PositiveIndex i))| = _
    simp only [(typeBRootPairing 2).pairingIn_reflectionPerm_self_left,
      (typeBRootPairing 2).pairingIn_reflectionPerm_self_right, abs_neg]
    rw [b2PositiveIndex_forwardPairing, b2PositiveIndex_reversePairing]
    exact ⟨rfl, rfl⟩

private lemma b2Root_isLongIndex_or_isShortIndex (r : TypeBRootIndex 2) :
    (typeBRootPairing 2).IsLongIndex r ∨
      (typeBRootPairing 2).IsShortIndex r := by
  obtain ⟨i, hi⟩ := b2Root_abs_pairings_with_simple r
  fin_cases i
  · right
    rw [(typeBRootPairing 2).isShortIndex_iff]
    refine ⟨typeBSimpleRootIndex 0 1, ?_⟩
    have h := hi 1
    rw [h.1, h.2]
    norm_num [b2PositiveForwardPairing, b2PositiveReversePairing]
  · left
    rw [(typeBRootPairing 2).isLongIndex_iff]
    refine ⟨typeBSimpleRootIndex 0 0, ?_⟩
    have h := hi 0
    rw [h.1, h.2]
    norm_num [b2PositiveForwardPairing, b2PositiveReversePairing]
  · left
    rw [(typeBRootPairing 2).isLongIndex_iff]
    refine ⟨typeBSimpleRootIndex 0 0, ?_⟩
    have h := hi 0
    rw [h.1, h.2]
    norm_num [b2PositiveForwardPairing, b2PositiveReversePairing]
  · right
    rw [(typeBRootPairing 2).isShortIndex_iff]
    refine ⟨typeBSimpleRootIndex 0 1, ?_⟩
    have h := hi 1
    rw [h.1, h.2]
    norm_num [b2PositiveForwardPairing, b2PositiveReversePairing]

private lemma b2Simple_isLong_iff_matrixLong (i : Fin 2) :
    (typeBRootPairing 2).IsLongIndex (typeBSimpleRootIndex 0 i) ↔
      ExceptionalMatrixLong (typeBCartanMatrix 0) i := by
  rw [(typeBRootPairing 2).isLongIndex_iff, exceptionalMatrixLong_iff]
  fin_cases i
  · constructor
    · rintro ⟨r, hr⟩
      obtain ⟨j, hj⟩ := b2Root_abs_pairings_with_simple r
      have hj0 := hj 0
      change |(typeBRootPairing 2).pairingIn ℤ r (typeBSimpleRootIndex 0 0)| = _ ∧
        |(typeBRootPairing 2).pairingIn ℤ (typeBSimpleRootIndex 0 0) r| = _ at hj0
      change |(typeBRootPairing 2).pairingIn ℤ r (typeBSimpleRootIndex 0 0)| >
        |(typeBRootPairing 2).pairingIn ℤ (typeBSimpleRootIndex 0 0) r| at hr
      rw [hj0.1, hj0.2] at hr
      fin_cases j <;>
        norm_num [b2PositiveForwardPairing, b2PositiveReversePairing] at hr
    · rintro ⟨j, hj⟩
      fin_cases j <;>
        norm_num [typeBCartanMatrix, Fin.last] at hj
  · constructor
    · intro _
      exact ⟨0, by
        norm_num [typeBCartanMatrix]
        simp⟩
    · intro _
      refine ⟨b2PositiveIndex 0, ?_⟩
      rw [b2PositiveIndex_forwardPairing, b2PositiveIndex_reversePairing]
      norm_num [b2PositiveForwardPairing, b2PositiveReversePairing]

private lemma b2Simple_isShort_iff_matrixShort (i : Fin 2) :
    (typeBRootPairing 2).IsShortIndex (typeBSimpleRootIndex 0 i) ↔
      ExceptionalMatrixShort (typeBCartanMatrix 0) i := by
  rw [(typeBRootPairing 2).isShortIndex_iff, exceptionalMatrixShort_iff]
  fin_cases i
  · constructor
    · intro _
      exact ⟨1, by
        norm_num [typeBCartanMatrix]
        simp⟩
    · intro _
      refine ⟨b2PositiveIndex 1, ?_⟩
      rw [b2PositiveIndex_forwardPairing, b2PositiveIndex_reversePairing]
      norm_num [b2PositiveForwardPairing, b2PositiveReversePairing]
  · constructor
    · rintro ⟨r, hr⟩
      obtain ⟨j, hj⟩ := b2Root_abs_pairings_with_simple r
      have hj1 := hj 1
      change |(typeBRootPairing 2).pairingIn ℤ r (typeBSimpleRootIndex 0 1)| = _ ∧
        |(typeBRootPairing 2).pairingIn ℤ (typeBSimpleRootIndex 0 1) r| = _ at hj1
      change |(typeBRootPairing 2).pairingIn ℤ (typeBSimpleRootIndex 0 1) r| >
        |(typeBRootPairing 2).pairingIn ℤ r (typeBSimpleRootIndex 0 1)| at hr
      rw [hj1.1, hj1.2] at hr
      fin_cases j <;>
        norm_num [b2PositiveForwardPairing, b2PositiveReversePairing] at hr
    · rintro ⟨j, hj⟩
      fin_cases j <;>
        norm_num [typeBCartanMatrix, Fin.last] at hj

private lemma b2PositiveIndex_coxeterFingerprint (i : Fin 4) (k : Fin 2) :
    (typeBRootPairing 2).pairingIn ℤ (b2PositiveIndex i)
          (typeBSimpleRootIndex 0 k) *
        (typeBRootPairing 2).pairingIn ℤ (typeBSimpleRootIndex 0 k)
          (b2PositiveIndex i) =
      b2PositiveCoxeterFingerprint i k := by
  rw [b2PositiveIndex_forwardPairing, b2PositiveIndex_reversePairing]
  fin_cases i <;> fin_cases k <;>
    norm_num [b2PositiveForwardPairing, b2PositiveReversePairing,
      b2PositiveCoxeterFingerprint]

set_option maxHeartbeats 800000 in
private lemma b2PositiveCoxeterFingerprint_injective :
    ∀ i j : Fin 4,
      (∀ k, b2PositiveCoxeterFingerprint i k =
        b2PositiveCoxeterFingerprint j k) → i = j := by
  have himp : ∀ i j : Fin 4,
      (∀ k, b2PositiveCoxeterFingerprint i k =
        b2PositiveCoxeterFingerprint j k) →
      ∀ k, exceptionalAbsoluteCartanFingerprint (typeBCartanMatrix 0)
          (typeB2PositiveCoeffs i) k =
        exceptionalAbsoluteCartanFingerprint (typeBCartanMatrix 0)
          (typeB2PositiveCoeffs j) k := by
    intro i j h
    have h0 := h (0 : Fin 2)
    have h1 := h (1 : Fin 2)
    simp_rw [exceptionalAbsoluteCartanFingerprint_apply]
    fin_cases i <;> fin_cases j <;>
      simp_all [b2PositiveCoxeterFingerprint, typeB2PositiveCoeffs,
        typeBCartanMatrix, Fin.sum_univ_two]
  intro i j h
  exact typeB2_positive_fingerprint_injective i j (himp i j h)

private lemma isPos_indexEquiv_of_isPos
    {ι ι₂ M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced]
    (base : P.Base) (base₂ : Q.Base) (e : P.Equiv Q)
    (eBase : base.support ≃ base₂.support)
    (heBase : ∀ i : base.support, e.indexEquiv i = eBase i)
    {x : ι} (hx : base.IsPos x) :
    base₂.IsPos (e.indexEquiv x) := by
  rw [base.isPos_iff_root_mem_closure] at hx
  rw [base₂.isPos_iff_root_mem_closure]
  rw [← RootPairing.Hom.root_weightMap_apply P Q x e.toHom]
  generalize P.root x = z at hx ⊢
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy =>
      rcases hy with ⟨j, hj, rfl⟩
      apply AddSubmonoid.subset_closure
      refine ⟨e.indexEquiv j, ?_, ?_⟩
      · rw [heBase ⟨j, hj⟩]
        exact (eBase ⟨j, hj⟩).property
      · exact (RootPairing.Hom.root_weightMap_apply P Q j e.toHom).symm
  | zero => simp
  | add y z hy hz ihy ihz =>
      simpa using AddSubmonoid.add_mem _ ihy ihz

/-- Every root of a pairing with the numbered `B₂` Cartan matrix belongs to
one of the two directed root-length classes. -/
public theorem exceptional_b2_isLongIndex_or_isShortIndex_of_cartan
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (numbering : base.support ≃ Fin 2)
    (hCartan : ∀ i j,
      P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
        typeBCartanMatrix 0 i j)
    (α : ι) : P.IsLongIndex α ∨ P.IsShortIndex α := by
  let model := typeBRootPairing 2
  let modelBase := typeBRootPairing_base 0
  let eBase : base.support ≃ modelBase.support :=
    numbering.trans (typeBRootPairing_baseEquiv 0)
  have hcartan : ∀ i j, modelBase.cartanMatrix (eBase i) (eBase j) =
      base.cartanMatrix i j := by
    intro i j
    rw [show eBase i = typeBRootPairing_baseEquiv 0 (numbering i) by rfl,
      show eBase j = typeBRootPairing_baseEquiv 0 (numbering j) by rfl,
      typeBRootPairing_base_cartanMatrix]
    change typeBCartanMatrix 0 (numbering i) (numbering j) =
      P.pairingIn ℤ i j
    simpa using (hCartan (numbering i) (numbering j)).symm
  let e : P.Equiv model :=
    base.equivOfCartanMatrixEq modelBase eBase hcartan
  have epairing (i j : ι) :
      model.pairingIn ℤ (e.indexEquiv i) (e.indexEquiv j) =
        P.pairingIn ℤ i j := by
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
    change algebraMap ℤ ℝ
        (model.pairingIn ℤ (e.indexEquiv i) (e.indexEquiv j)) =
      algebraMap ℤ ℝ (P.pairingIn ℤ i j)
    rw [model.algebraMap_pairingIn, P.algebraMap_pairingIn]
    exact RootPairing.Equiv.pairing_eq e i j
  rcases b2Root_isLongIndex_or_isShortIndex (e.indexEquiv α) with hα | hα
  · left
    rw [P.isLongIndex_iff]
    rw [model.isLongIndex_iff] at hα
    obtain ⟨y, hy⟩ := hα
    obtain ⟨β, rfl⟩ := e.indexEquiv.surjective y
    exact ⟨β, by simpa only [epairing] using hy⟩
  · right
    rw [P.isShortIndex_iff]
    rw [model.isShortIndex_iff] at hα
    obtain ⟨y, hy⟩ := hα
    obtain ⟨β, rfl⟩ := e.indexEquiv.surjective y
    exact ⟨β, by simpa only [epairing] using hy⟩

private theorem exceptional_b2_positiveRootDuality_unique_of_cartan
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (numbering : base.support ≃ Fin 2)
    (hCartan : ∀ i j,
      P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
        typeBCartanMatrix 0 i j)
    {ρ σ : Equiv.Perm ι}
    (hρ : P.IsPositiveRootDuality base ρ)
    (hσ : P.IsPositiveRootDuality base σ) :
    ρ = σ := by
  let _ := P.indexNeg
  let model := typeBRootPairing 2
  let _ := model.indexNeg
  let modelBase := typeBRootPairing_base 0
  let eBase : base.support ≃ modelBase.support :=
    numbering.trans (typeBRootPairing_baseEquiv 0)
  have hcartan : ∀ i j, modelBase.cartanMatrix (eBase i) (eBase j) =
      base.cartanMatrix i j := by
    intro i j
    rw [show eBase i = typeBRootPairing_baseEquiv 0 (numbering i) by rfl,
      show eBase j = typeBRootPairing_baseEquiv 0 (numbering j) by rfl,
      typeBRootPairing_base_cartanMatrix]
    change typeBCartanMatrix 0 (numbering i) (numbering j) =
      P.pairingIn ℤ i j
    simpa using (hCartan (numbering i) (numbering j)).symm
  let e : P.Equiv model :=
    base.equivOfCartanMatrixEq modelBase eBase hcartan
  have heBase' (i : base.support) : e.indexEquiv i = eBase i := by
    apply model.root.injective
    rw [← RootPairing.Hom.root_weightMap_apply P model i e.toHom]
    change (base.toWeightBasis.equiv modelBase.toWeightBasis eBase) (P.root i) =
      model.root (eBase i)
    simp [Module.Basis.equiv, model]
  have heBase (i : Fin 2) :
      e.indexEquiv (numbering.symm i) = typeBSimpleRootIndex 0 i := by
    rw [heBase']
    change (typeBRootPairing_baseEquiv 0
      (numbering (numbering.symm i)) : TypeBRootIndex 2) = _
    rw [numbering.apply_symm_apply, typeBRootPairing_baseEquiv_val]
  have epairing (i j : ι) :
      model.pairingIn ℤ (e.indexEquiv i) (e.indexEquiv j) =
        P.pairingIn ℤ i j := by
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
    change algebraMap ℤ ℝ (model.pairingIn ℤ (e.indexEquiv i) (e.indexEquiv j)) =
      algebraMap ℤ ℝ (P.pairingIn ℤ i j)
    rw [model.algebraMap_pairingIn, P.algebraMap_pairingIn]
    exact RootPairing.Equiv.pairing_eq e i j
  have elong (x : ι) :
      P.IsLongIndex x ↔ model.IsLongIndex (e.indexEquiv x) := by
    rw [P.isLongIndex_iff, model.isLongIndex_iff]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e.indexEquiv y, by simpa only [epairing] using hy⟩
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := e.indexEquiv.surjective y
      exact ⟨z, by simpa only [epairing] using hy⟩
  have eshort (x : ι) :
      P.IsShortIndex x ↔ model.IsShortIndex (e.indexEquiv x) := by
    rw [P.isShortIndex_iff, model.isShortIndex_iff]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e.indexEquiv y, by simpa only [epairing] using hy⟩
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := e.indexEquiv.surjective y
      exact ⟨z, by simpa only [epairing] using hy⟩
  have hLong (i : Fin 2) :
      P.IsLongIndex (numbering.symm i) ↔
        ExceptionalMatrixLong (typeBCartanMatrix 0) i := by
    rw [elong, heBase, b2Simple_isLong_iff_matrixLong]
  have hShort (i : Fin 2) :
      P.IsShortIndex (numbering.symm i) ↔
        ExceptionalMatrixShort (typeBCartanMatrix 0) i := by
    rw [eshort, heBase, b2Simple_isShort_iff_matrixShort]
  have hρ' := (P.isPositiveRootDuality_iff base ρ).mp hρ
  have hσ' := (P.isPositiveRootDuality_iff base σ).mp hσ
  rcases hρ' with ⟨hρsupport, hρpos, _, _, hρproduct⟩
  rcases hσ' with ⟨hσsupport, hσpos, _, _, hσproduct⟩
  have hρNumbered := exceptional_base_perm_eq_reverse_of_matrix_check
    (typeBCartanMatrix 0) exceptional_b2_matrix_duality_unique base numbering ρ
      hρsupport hLong hShort hCartan hρ
  have hσNumbered := exceptional_base_perm_eq_reverse_of_matrix_check
    (typeBCartanMatrix 0) exceptional_b2_matrix_duality_unique base numbering σ
      hσsupport hLong hShort hCartan hσ
  have hρBase (i : Fin 2) :
      ρ (numbering.symm i) = numbering.symm (Fin.revPerm i) := by
    have hi := hρNumbered i
    have hi' := congrArg (fun j => ((numbering.symm j : base.support) : ι)) hi
    simpa using hi'
  have hσBase (i : Fin 2) :
      σ (numbering.symm i) = numbering.symm (Fin.revPerm i) := by
    have hi := hσNumbered i
    have hi' := congrArg (fun j => ((numbering.symm j : base.support) : ι)) hi
    simpa using hi'
  have eenumerate (x : ι) (hx : base.IsPos x) :
      ∃ i : Fin 4, e.indexEquiv x = b2PositiveIndex i := by
    have hx' : modelBase.IsPos (e.indexEquiv x) :=
      isPos_indexEquiv_of_isPos base modelBase e eBase heBase' hx
    exact b2PositiveIndex_surjective _ hx'
  apply Equiv.ext
  intro α
  have htargetProduct (k : Fin 2) :
      P.pairingIn ℤ (ρ α) (numbering.symm k) *
          P.pairingIn ℤ (numbering.symm k) (ρ α) =
        P.pairingIn ℤ (σ α) (numbering.symm k) *
          P.pairingIn ℤ (numbering.symm k) (σ α) := by
    have hρk := hρproduct α (numbering.symm (Fin.revPerm k))
    have hσk := hσproduct α (numbering.symm (Fin.revPerm k))
    have hrev : Fin.revPerm (Fin.revPerm k) = k := by
      fin_cases k <;> rfl
    rw [hρBase, hrev] at hρk
    rw [hσBase, hrev] at hσk
    exact hρk.trans hσk.symm
  by_cases hα : base.IsPos α
  · obtain ⟨i, hi⟩ := eenumerate (ρ α) ((hρpos α).mp hα)
    obtain ⟨j, hj⟩ := eenumerate (σ α) ((hσpos α).mp hα)
    have hij : i = j := b2PositiveCoxeterFingerprint_injective i j (by
      intro k
      rw [← b2PositiveIndex_coxeterFingerprint,
        ← b2PositiveIndex_coxeterFingerprint, ← hi, ← hj, ← heBase k]
      rw [epairing, epairing, epairing, epairing]
      exact htargetProduct k)
    apply e.indexEquiv.injective
    rw [hi, hj, hij]
  · have hρneg : ¬base.IsPos (ρ α) := by
      simpa only [hρpos α] using hα
    have hσneg : ¬base.IsPos (σ α) := by
      simpa only [hσpos α] using hα
    obtain ⟨i, hi⟩ := eenumerate (-ρ α)
      ((RootPairing.Base.IsPos.neg_iff_not base (ρ α)).mpr hρneg)
    obtain ⟨j, hj⟩ := eenumerate (-σ α)
      ((RootPairing.Base.IsPos.neg_iff_not base (σ α)).mpr hσneg)
    have hij : i = j := b2PositiveCoxeterFingerprint_injective i j (by
      intro k
      rw [← b2PositiveIndex_coxeterFingerprint,
        ← b2PositiveIndex_coxeterFingerprint, ← hi, ← hj, ← heBase k]
      rw [epairing, epairing, epairing, epairing]
      change
        P.pairingIn ℤ (P.reflectionPerm (ρ α) (ρ α)) (numbering.symm k) *
            P.pairingIn ℤ (numbering.symm k) (P.reflectionPerm (ρ α) (ρ α)) =
          P.pairingIn ℤ (P.reflectionPerm (σ α) (σ α)) (numbering.symm k) *
            P.pairingIn ℤ (numbering.symm k) (P.reflectionPerm (σ α) (σ α))
      simpa only [P.pairingIn_reflectionPerm_self_left,
        P.pairingIn_reflectionPerm_self_right, neg_mul_neg] using htargetProduct k)
    apply neg_injective
    apply e.indexEquiv.injective
    rw [hi, hj, hij]

public theorem exceptional_b2_positiveRootDuality_unique
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (classification : RootClassification)
    (numbering : base.support ≃ Fin classification.rank)
    (hbase : ∀ i j, base.cartanMatrixIn ℤ i j =
      dynkinCartanEntry classification (numbering i) (numbering j))
    (hB : classification.kind = .B ∧ classification.rank = 2)
    {ρ σ : Equiv.Perm ι}
    (hρ : P.IsPositiveRootDuality base ρ)
    (hσ : P.IsPositiveRootDuality base σ) :
    ρ = σ := by
  rcases classification with ⟨kind, rank⟩
  rcases hB with ⟨rfl, rfl⟩
  apply exceptional_b2_positiveRootDuality_unique_of_cartan base numbering
  intro i j
  have h := hbase (numbering.symm i) (numbering.symm j)
  rw [RootPairing.Base.cartanMatrixIn_def (S := ℤ)] at h
  fin_cases i <;> fin_cases j <;>
    simp [dynkinCartanEntry, typeBCartanMatrix] at h ⊢
  all_goals assumption

end Theory.AlgebraicGroup
