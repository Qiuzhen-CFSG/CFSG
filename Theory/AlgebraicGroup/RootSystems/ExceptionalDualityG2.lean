module

public import Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.Core

/-!
# The classified G2 exceptional-duality adapter

This module transports the finite standard-model calculations for `G₂` to an
arbitrary crystallographic reduced root pairing whose numbered base has the
standard `G₂` Cartan matrix.  It first reconstructs Mathlib's embedded `G₂`
model, enumerates its six positive roots, and identifies their absolute Cartan
fingerprints with the kernel-checked coefficient table from
`ExceptionalDuality`.

The main result then applies the standard matrix rigidity theorem to the simple
roots.  Preservation of positivity and Coxeter products reduces equality on all
roots to the transported fingerprint injection.  This supplies the `G₂`
uniqueness input for the exceptional graph-field duality argument.  The
embedded model's two simple-root lengths also give the long-or-short
exhaustiveness result exported below.
-/

namespace Theory.AlgebraicGroup

open Set
open StandardRootSystem

private lemma typeG2CartanMatrix_eq_dynkinCartanEntry (i j : Fin 2) :
    typeG2CartanMatrix i j = dynkinCartanEntry ⟨.G2, 2⟩ i j := by
  fin_cases i <;> fin_cases j <;> rfl

private noncomputable def g2PositiveRoot
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem] [P.EmbeddedG2] : Fin 6 → ι
  | ⟨0, _⟩ => RootPairing.EmbeddedG2.short P
  | ⟨1, _⟩ => RootPairing.EmbeddedG2.long P
  | ⟨2, _⟩ => RootPairing.EmbeddedG2.shortAddLong P
  | ⟨3, _⟩ => RootPairing.EmbeddedG2.twoShortAddLong P
  | ⟨4, _⟩ => RootPairing.EmbeddedG2.threeShortAddLong P
  | ⟨5, _⟩ => RootPairing.EmbeddedG2.threeShortAddTwoLong P

private lemma g2PositiveRoot_isPos
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem] [P.EmbeddedG2]
    (base : P.Base)
    (hshort : RootPairing.EmbeddedG2.short P ∈ base.support)
    (hlong : RootPairing.EmbeddedG2.long P ∈ base.support) :
    ∀ i : Fin 6, base.IsPos (g2PositiveRoot P i) := by
  have hs := base.isPos_of_mem_support hshort
  have hl := base.isPos_of_mem_support hlong
  have hsl : base.IsPos (RootPairing.EmbeddedG2.shortAddLong P) :=
    hs.add hl (RootPairing.EmbeddedG2.shortAddLongRoot_eq P)
  have h2sl : base.IsPos (RootPairing.EmbeddedG2.twoShortAddLong P) := by
    apply hs.add hsl
    calc
      P.root (RootPairing.EmbeddedG2.twoShortAddLong P) =
          (2 : ℝ) • P.root (RootPairing.EmbeddedG2.short P) +
            P.root (RootPairing.EmbeddedG2.long P) :=
        RootPairing.EmbeddedG2.twoShortAddLongRoot_eq P
      _ = P.root (RootPairing.EmbeddedG2.short P) +
          P.root (RootPairing.EmbeddedG2.shortAddLong P) := by
        calc
          _ = P.root (RootPairing.EmbeddedG2.short P) +
              (P.root (RootPairing.EmbeddedG2.short P) +
                P.root (RootPairing.EmbeddedG2.long P)) := by module
          _ = _ := congrArg (P.root (RootPairing.EmbeddedG2.short P) + ·)
            (RootPairing.EmbeddedG2.shortAddLongRoot_eq P).symm
  have h3sl : base.IsPos (RootPairing.EmbeddedG2.threeShortAddLong P) := by
    apply hs.add h2sl
    calc
      P.root (RootPairing.EmbeddedG2.threeShortAddLong P) =
          (3 : ℝ) • P.root (RootPairing.EmbeddedG2.short P) +
            P.root (RootPairing.EmbeddedG2.long P) :=
        RootPairing.EmbeddedG2.threeShortAddLongRoot_eq P
      _ = P.root (RootPairing.EmbeddedG2.short P) +
          P.root (RootPairing.EmbeddedG2.twoShortAddLong P) := by
        calc
          _ = P.root (RootPairing.EmbeddedG2.short P) +
              ((2 : ℝ) • P.root (RootPairing.EmbeddedG2.short P) +
                P.root (RootPairing.EmbeddedG2.long P)) := by module
          _ = _ := congrArg (P.root (RootPairing.EmbeddedG2.short P) + ·)
            (RootPairing.EmbeddedG2.twoShortAddLongRoot_eq P).symm
  have h3s2l : base.IsPos (RootPairing.EmbeddedG2.threeShortAddTwoLong P) := by
    apply hl.add h3sl
    calc
      P.root (RootPairing.EmbeddedG2.threeShortAddTwoLong P) =
          (3 : ℝ) • P.root (RootPairing.EmbeddedG2.short P) +
            (2 : ℝ) • P.root (RootPairing.EmbeddedG2.long P) :=
        RootPairing.EmbeddedG2.threeShortAddTwoLongRoot_eq P
      _ = P.root (RootPairing.EmbeddedG2.long P) +
          P.root (RootPairing.EmbeddedG2.threeShortAddLong P) := by
        calc
          _ = P.root (RootPairing.EmbeddedG2.long P) +
              ((3 : ℝ) • P.root (RootPairing.EmbeddedG2.short P) +
                P.root (RootPairing.EmbeddedG2.long P)) := by module
          _ = _ := congrArg (P.root (RootPairing.EmbeddedG2.long P) + ·)
            (RootPairing.EmbeddedG2.threeShortAddLongRoot_eq P).symm
  intro i
  fin_cases i <;> simp_all [g2PositiveRoot]

private lemma g2PositiveRoot_surjective
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsIrreducible] [P.EmbeddedG2]
    (base : P.Base)
    (hshort : RootPairing.EmbeddedG2.short P ∈ base.support)
    (hlong : RootPairing.EmbeddedG2.long P ∈ base.support)
    {α : ι} (hα : base.IsPos α) :
    ∃ i : Fin 6, α = g2PositiveRoot P i := by
  let := P.indexNeg
  have hcandidate := g2PositiveRoot_isPos P base hshort hlong
  have hnotneg (i : Fin 6) : α ≠ -g2PositiveRoot P i := by
    intro h
    subst α
    exact (RootPairing.Base.IsPos.neg_iff_not base (g2PositiveRoot P i)).mp hα
      (hcandidate i)
  have hall := RootPairing.EmbeddedG2.mem_allRoots P α
  simp only [RootPairing.EmbeddedG2.allRoots, List.mem_cons, List.not_mem_nil,
    or_false] at hall
  rcases hall with h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨1, P.root.injective h⟩
  · exact (hnotneg 1 (P.root.injective (by simpa [g2PositiveRoot] using h))).elim
  · exact ⟨0, P.root.injective h⟩
  · exact (hnotneg 0 (P.root.injective (by simpa [g2PositiveRoot] using h))).elim
  · exact ⟨2, P.root.injective h⟩
  · exact (hnotneg 2 (P.root.injective (by simpa [g2PositiveRoot] using h))).elim
  · exact ⟨3, P.root.injective h⟩
  · exact (hnotneg 3 (P.root.injective (by simpa [g2PositiveRoot] using h))).elim
  · exact ⟨4, P.root.injective h⟩
  · exact (hnotneg 4 (P.root.injective (by simpa [g2PositiveRoot] using h))).elim
  · exact ⟨5, P.root.injective h⟩
  · exact (hnotneg 5 (P.root.injective (by simpa [g2PositiveRoot] using h))).elim

private lemma g2SimpleRoot_lengthClasses
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsIrreducible] [P.EmbeddedG2] :
    (P.IsLongIndex (RootPairing.EmbeddedG2.short P) ∧
      ¬ P.IsShortIndex (RootPairing.EmbeddedG2.short P)) ∧
    (¬ P.IsLongIndex (RootPairing.EmbeddedG2.long P) ∧
      P.IsShortIndex (RootPairing.EmbeddedG2.long P)) := by
  let := P.indexNeg
  have hshortLong : P.IsLongIndex (RootPairing.EmbeddedG2.short P) := by
    rw [P.isLongIndex_iff]
    exact ⟨RootPairing.EmbeddedG2.long P, by simp⟩
  have hlongShort : P.IsShortIndex (RootPairing.EmbeddedG2.long P) := by
    rw [P.isShortIndex_iff]
    exact ⟨RootPairing.EmbeddedG2.short P, by simp⟩
  refine ⟨⟨hshortLong, ?_⟩, ⟨?_, hlongShort⟩⟩
  · rw [P.isShortIndex_iff]
    rintro ⟨β, hβ⟩
    have hall := RootPairing.EmbeddedG2.mem_allRoots P β
    simp only [RootPairing.EmbeddedG2.allRoots, List.mem_cons, List.not_mem_nil,
      or_false] at hall
    rcases hall with h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp only [EmbeddingLike.apply_eq_iff_eq, P.root_eq_neg_iff] at h <;>
      subst β <;> simp at hβ
  · rw [P.isLongIndex_iff]
    rintro ⟨β, hβ⟩
    have hall := RootPairing.EmbeddedG2.mem_allRoots P β
    simp only [RootPairing.EmbeddedG2.allRoots, List.mem_cons, List.not_mem_nil,
      or_false] at hall
    rcases hall with h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp only [EmbeddingLike.apply_eq_iff_eq, P.root_eq_neg_iff] at h <;>
      subst β <;> simp at hβ

/-- Every root of an irreducible pairing with the numbered `G₂` Cartan matrix
belongs to one of the two directed root-length classes. -/
public theorem exceptional_g2_isLongIndex_or_isShortIndex_of_cartan
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (base : P.Base) (numbering : base.support ≃ Fin 2)
    (hCartan : ∀ i j,
      P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
        typeG2CartanMatrix i j)
    (α : ι) : P.IsLongIndex α ∨ P.IsShortIndex α := by
  classical
  let _ := Fintype.ofFinite ι
  let : P.EmbeddedG2 :=
    { long := numbering.symm 1
      short := numbering.symm 0
      pairingIn_long_short := by
        rw [hCartan]
        norm_num [typeG2CartanMatrix] }
  let B := (P.posRootForm ℤ).toInvariantForm
  have hratio :
      B.form (P.root (RootPairing.EmbeddedG2.long P))
          (P.root (RootPairing.EmbeddedG2.long P)) =
        (3 : ℝ) *
          B.form (P.root (RootPairing.EmbeddedG2.short P))
            (P.root (RootPairing.EmbeddedG2.short P)) := by
    have hrel := B.pairing_mul_eq_pairing_mul_swap
      (RootPairing.EmbeddedG2.short P) (RootPairing.EmbeddedG2.long P)
    simp only [← P.algebraMap_pairingIn ℤ] at hrel
    norm_num at hrel ⊢
    linarith
  have hne :
      B.form (P.root (RootPairing.EmbeddedG2.short P))
          (P.root (RootPairing.EmbeddedG2.short P)) ≠
        B.form (P.root (RootPairing.EmbeddedG2.long P))
          (P.root (RootPairing.EmbeddedG2.long P)) := by
    intro h
    rw [h] at hratio
    exact B.ne_zero (RootPairing.EmbeddedG2.long P) (by linarith)
  have hlength (β : ι) :
      B.form (P.root β) (P.root β) =
          B.form (P.root (RootPairing.EmbeddedG2.short P))
            (P.root (RootPairing.EmbeddedG2.short P)) ∨
        B.form (P.root β) (P.root β) =
          B.form (P.root (RootPairing.EmbeddedG2.long P))
            (P.root (RootPairing.EmbeddedG2.long P)) :=
    B.apply_eq_or_of_apply_ne hne β
  exact P.isLongIndex_or_isShortIndex_of_two_form_lengths B
    (RootPairing.EmbeddedG2.short P) (RootPairing.EmbeddedG2.long P)
    3 (by norm_num) hratio hlength α

private lemma g2PositiveRoot_pairingIn
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem] [P.EmbeddedG2]
    (numbering : Fin 2 → ι)
    (hzero : numbering 0 = RootPairing.EmbeddedG2.short P)
    (hone : numbering 1 = RootPairing.EmbeddedG2.long P)
    (i : Fin 6) (j : Fin 2) :
    P.pairingIn ℤ (g2PositiveRoot P i) (numbering j) =
      ∑ k : Fin 2, typeG2PositiveCoeffs i k * typeG2CartanMatrix k j := by
  fin_cases i <;> fin_cases j <;>
    simp [g2PositiveRoot, typeG2PositiveCoeffs, typeG2CartanMatrix,
      Fin.sum_univ_two, hzero, hone]

private lemma g2PositiveRoot_absPairing_eq_of_coxeter
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsIrreducible] [P.EmbeddedG2]
    (base : P.Base) (numbering : Fin 2 → ι)
    (hzero : numbering 0 = RootPairing.EmbeddedG2.short P)
    (hone : numbering 1 = RootPairing.EmbeddedG2.long P)
    (hshort : RootPairing.EmbeddedG2.short P ∈ base.support)
    (hlong : RootPairing.EmbeddedG2.long P ∈ base.support)
    {α β : ι} (hα : base.IsPos α) (hβ : base.IsPos β)
    (hcox : ∀ j : Fin 2,
      P.pairingIn ℤ α (numbering j) * P.pairingIn ℤ (numbering j) α =
        P.pairingIn ℤ β (numbering j) * P.pairingIn ℤ (numbering j) β) :
    ∀ j : Fin 2,
      |P.pairingIn ℤ α (numbering j)| = |P.pairingIn ℤ β (numbering j)| := by
  obtain ⟨i, rfl⟩ := g2PositiveRoot_surjective P base hshort hlong hα
  obtain ⟨k, rfl⟩ := g2PositiveRoot_surjective P base hshort hlong hβ
  have hcox0 := hcox 0
  have hcox1 := hcox 1
  intro j
  fin_cases i <;> fin_cases k <;> fin_cases j <;>
    simp [g2PositiveRoot, hzero, hone] at hcox0 hcox1 ⊢

public theorem exceptional_g2_positive_fingerprint_injective
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (numbering : base.support ≃ Fin 2)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
      typeG2CartanMatrix i j)
    {α β : ι} (hα : base.IsPos α) (hβ : base.IsPos β)
    (hfp : ∀ j : Fin 2,
      |P.pairingIn ℤ α (numbering.symm j)| =
        |P.pairingIn ℤ β (numbering.symm j)|) :
    α = β := by
  classical
  have hType : HasDynkinType P ⟨.G2, 2⟩ := by
    refine ⟨base, numbering, ?_⟩
    intro i j
    change P.pairingIn ℤ i j = _
    calc
      P.pairingIn ℤ i j = typeG2CartanMatrix (numbering i) (numbering j) := by
        simpa using hCartan (numbering i) (numbering j)
      _ = dynkinCartanEntry ⟨.G2, 2⟩ (numbering i) (numbering j) :=
        typeG2CartanMatrix_eq_dynkinCartanEntry _ _
  let : P.IsIrreducible := isIrreducible_of_hasDynkinType_g2 P hType
  let : P.EmbeddedG2 :=
    { long := numbering.symm 1
      short := numbering.symm 0
      pairingIn_long_short := by
        rw [hCartan]
        norm_num [typeG2CartanMatrix] }
  have hshort : RootPairing.EmbeddedG2.short P ∈ base.support :=
    (numbering.symm 0).property
  have hlong : RootPairing.EmbeddedG2.long P ∈ base.support :=
    (numbering.symm 1).property
  obtain ⟨i, rfl⟩ := g2PositiveRoot_surjective P base hshort hlong hα
  obtain ⟨j, rfl⟩ := g2PositiveRoot_surjective P base hshort hlong hβ
  apply congrArg (g2PositiveRoot P)
  apply typeG2_positive_fingerprint_injective i j
  intro k
  rw [exceptionalAbsoluteCartanFingerprint_apply,
    exceptionalAbsoluteCartanFingerprint_apply]
  rw [← g2PositiveRoot_pairingIn P (fun j => (numbering.symm j : ι)) rfl rfl]
  rw [← g2PositiveRoot_pairingIn P (fun j => (numbering.symm j : ι)) rfl rfl]
  exact hfp k

private lemma g2Root_eq_of_sign_and_coxeter
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsIrreducible] [P.EmbeddedG2]
    (base : P.Base) (numbering : base.support ≃ Fin 2)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
      typeG2CartanMatrix i j)
    (hzero : (numbering.symm 0 : ι) = RootPairing.EmbeddedG2.short P)
    (hone : (numbering.symm 1 : ι) = RootPairing.EmbeddedG2.long P)
    (hshort : RootPairing.EmbeddedG2.short P ∈ base.support)
    (hlong : RootPairing.EmbeddedG2.long P ∈ base.support)
    {α β : ι} (hsign : base.IsPos α ↔ base.IsPos β)
    (hcox : ∀ j : Fin 2,
      P.pairingIn ℤ α (numbering.symm j) *
          P.pairingIn ℤ (numbering.symm j) α =
        P.pairingIn ℤ β (numbering.symm j) *
          P.pairingIn ℤ (numbering.symm j) β) :
    α = β := by
  by_cases hα : base.IsPos α
  · have hβ := hsign.mp hα
    apply exceptional_g2_positive_fingerprint_injective base numbering hCartan hα hβ
    exact g2PositiveRoot_absPairing_eq_of_coxeter P base
      (fun j => (numbering.symm j : ι)) hzero hone hshort hlong hα hβ hcox
  · let := P.indexNeg
    have hβ : ¬ base.IsPos β := fun h => hα (hsign.mpr h)
    have hnα : base.IsPos (-α) :=
      (RootPairing.Base.IsPos.neg_iff_not base α).mpr hα
    have hnβ : base.IsPos (-β) :=
      (RootPairing.Base.IsPos.neg_iff_not base β).mpr hβ
    have hcoxNeg : ∀ j : Fin 2,
        P.pairingIn ℤ (-α) (numbering.symm j) *
            P.pairingIn ℤ (numbering.symm j) (-α) =
          P.pairingIn ℤ (-β) (numbering.symm j) *
            P.pairingIn ℤ (numbering.symm j) (-β) := by
      intro j
      simpa using hcox j
    have hneg : -α = -β := by
      apply exceptional_g2_positive_fingerprint_injective base numbering hCartan hnα hnβ
      exact g2PositiveRoot_absPairing_eq_of_coxeter P base
        (fun j => (numbering.symm j : ι)) hzero hone hshort hlong hnα hnβ hcoxNeg
    exact neg_injective hneg

public theorem exceptional_g2_root_duality_unique
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (numbering : base.support ≃ Fin 2)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) =
      typeG2CartanMatrix i j)
    {ρ σ : Equiv.Perm ι}
    (hρ : P.IsPositiveRootDuality base ρ)
    (hσ : P.IsPositiveRootDuality base σ) :
    ρ = σ := by
  classical
  have hType : HasDynkinType P ⟨.G2, 2⟩ := by
    refine ⟨base, numbering, ?_⟩
    intro i j
    change P.pairingIn ℤ i j = _
    calc
      P.pairingIn ℤ i j = typeG2CartanMatrix (numbering i) (numbering j) := by
        simpa using hCartan (numbering i) (numbering j)
      _ = dynkinCartanEntry ⟨.G2, 2⟩ (numbering i) (numbering j) :=
        typeG2CartanMatrix_eq_dynkinCartanEntry _ _
  let : P.IsIrreducible := isIrreducible_of_hasDynkinType_g2 P hType
  let : P.EmbeddedG2 :=
    { long := numbering.symm 1
      short := numbering.symm 0
      pairingIn_long_short := by
        rw [hCartan]
        norm_num [typeG2CartanMatrix] }
  have hshort : RootPairing.EmbeddedG2.short P ∈ base.support :=
    (numbering.symm 0).property
  have hlong : RootPairing.EmbeddedG2.long P ∈ base.support :=
    (numbering.symm 1).property
  have hclasses := g2SimpleRoot_lengthClasses P
  have hLong : ∀ i, P.IsLongIndex (numbering.symm i) ↔
      ExceptionalMatrixLong typeG2CartanMatrix i := by
    intro i
    fin_cases i
    · change P.IsLongIndex (RootPairing.EmbeddedG2.short P) ↔ _
      constructor
      · intro _
        rw [exceptionalMatrixLong_iff]
        exact ⟨1, by norm_num [typeG2CartanMatrix]⟩
      · intro _
        exact hclasses.1.1
    · change P.IsLongIndex (RootPairing.EmbeddedG2.long P) ↔ _
      constructor
      · exact fun h => (hclasses.2.1 h).elim
      · rw [exceptionalMatrixLong_iff]
        rintro ⟨j, hj⟩
        fin_cases j <;> norm_num [typeG2CartanMatrix] at hj
  have hShort : ∀ i, P.IsShortIndex (numbering.symm i) ↔
      ExceptionalMatrixShort typeG2CartanMatrix i := by
    intro i
    fin_cases i
    · change P.IsShortIndex (RootPairing.EmbeddedG2.short P) ↔ _
      constructor
      · exact fun h => (hclasses.1.2 h).elim
      · rw [exceptionalMatrixShort_iff]
        rintro ⟨j, hj⟩
        fin_cases j <;> norm_num [typeG2CartanMatrix] at hj
    · change P.IsShortIndex (RootPairing.EmbeddedG2.long P) ↔ _
      constructor
      · intro _
        rw [exceptionalMatrixShort_iff]
        exact ⟨0, by norm_num [typeG2CartanMatrix]⟩
      · intro _
        exact hclasses.2.2
  have hbase
      (τ : Equiv.Perm ι) (hτ : P.IsPositiveRootDuality base τ) (i : Fin 2) :
      τ (numbering.symm i) = numbering.symm (Fin.revPerm i) := by
    have hτ' := (P.isPositiveRootDuality_iff base τ).mp hτ
    have hi := exceptional_base_perm_eq_reverse_of_matrix_check
      typeG2CartanMatrix exceptional_g2_matrix_duality_unique base numbering τ hτ'.1
      hLong hShort hCartan hτ i
    have hi' := congrArg numbering.symm hi
    exact congrArg Subtype.val (by simpa using hi')
  apply Equiv.ext
  intro α
  rcases (P.isPositiveRootDuality_iff base ρ).mp hρ with
    ⟨_, hposρ, _, _, hangleρ⟩
  rcases (P.isPositiveRootDuality_iff base σ).mp hσ with
    ⟨_, hposσ, _, _, hangleσ⟩
  apply g2Root_eq_of_sign_and_coxeter base numbering hCartan rfl rfl hshort hlong
  · exact (hposρ α).symm.trans (hposσ α)
  · intro i
    fin_cases i
    · have hr := hangleρ α (numbering.symm 1)
      have hs := hangleσ α (numbering.symm 1)
      rw [hbase ρ hρ 1] at hr
      rw [hbase σ hσ 1] at hs
      simpa [Fin.revPerm] using hr.trans hs.symm
    · have hr := hangleρ α (numbering.symm 0)
      have hs := hangleσ α (numbering.symm 0)
      rw [hbase ρ hρ 0] at hr
      rw [hbase σ hσ 0] at hs
      simpa [Fin.revPerm] using hr.trans hs.symm

end Theory.AlgebraicGroup
