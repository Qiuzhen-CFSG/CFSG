module

public import Theory.AlgebraicGroup.RootSystems.Classification
public import Theory.AlgebraicGroup.RootSystems.PositiveSubsystem
public meta import Theory.AlgebraicGroup.RootSystems.Exceptional

/-!
# Exceptional duality fingerprints

This module packages the root-length predicates used by the exceptional
duality argument and records the finite Cartan-matrix checks for the standard
`B₂`, `F₄`, and `G₂` numberings.  The finite checks are deliberately stated at
the matrix level: they are kernel-checked enumerations of the permutations of
the numbered simple roots, together with the positive coefficient lists and
absolute Cartan fingerprints of the standard positive roots.  They can
therefore be reused after transporting an arbitrary root pairing to a standard
model.  The matrix lemmas are the finite rigidity layer; model-adapter lemmas
transport them to classified pairings, while the separate existence layer
constructs the flipped positive system.  The invariant-form bridge below turns
an exhaustive two-length calculation into the directed integral-pairing
predicates used by those adapters.
-/

namespace Theory.AlgebraicGroup

open Set
open StandardRootSystem

public def _root_.RootPairing.IsLongIndex
    {ι M N : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsCrystallographic] (α : ι) : Prop :=
  ∃ β, |P.pairingIn ℤ β α| > |P.pairingIn ℤ α β|

public lemma _root_.RootPairing.isLongIndex_iff
    {ι M N : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsCrystallographic] (α : ι) :
    P.IsLongIndex α ↔ ∃ β, |P.pairingIn ℤ β α| > |P.pairingIn ℤ α β| := by
  rfl

public def _root_.RootPairing.IsShortIndex
    {ι M N : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsCrystallographic] (α : ι) : Prop :=
  ∃ β, |P.pairingIn ℤ α β| > |P.pairingIn ℤ β α|

public lemma _root_.RootPairing.isShortIndex_iff
    {ι M N : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsCrystallographic] (α : ι) :
    P.IsShortIndex α ↔ ∃ β, |P.pairingIn ℤ α β| > |P.pairingIn ℤ β α| := by
  rfl

/-- An irreducible reduced crystallographic root pairing with two prescribed
root lengths and a nontrivial integral ratio has only long or short indices.

For a root in either length class, irreducibility supplies a nonorthogonal root
in the other class.  Invariance of the form identifies the two directed Cartan
pairings up to the length ratio, and nonorthogonality makes the smaller pairing
nonzero, so their absolute values are strictly ordered. -/
public theorem _root_.RootPairing.isLongIndex_or_isShortIndex_of_two_form_lengths
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (B : P.InvariantForm) (short long : ι) (q : ℤ) (hq : 1 < q)
    (hratio : B.form (P.root long) (P.root long) =
      (q : ℝ) * B.form (P.root short) (P.root short))
    (hlength : ∀ α,
      B.form (P.root α) (P.root α) =
          B.form (P.root short) (P.root short) ∨
        B.form (P.root α) (P.root α) =
          B.form (P.root long) (P.root long))
    (α : ι) : P.IsLongIndex α ∨ P.IsShortIndex α := by
  classical
  have hqabs : 1 < |q| := by simpa [abs_of_pos (by omega : 0 < q)] using hq
  have pairingIn_ne_of_form_ne {i j : ι}
      (hij : B.form (P.root i) (P.root j) ≠ 0) :
      P.pairingIn ℤ i j ≠ 0 := by
    intro hpair
    apply hij
    rw [B.apply_root_root_zero_iff]
    rw [← P.algebraMap_pairingIn ℤ, hpair, map_zero]
  rcases hlength α with hα | hα
  · left
    rw [P.isLongIndex_iff]
    obtain ⟨k, hklen, hkform⟩ :=
      P.exists_form_eq_form_and_form_ne_zero B α long
    refine ⟨k, ?_⟩
    have hshort : B.form (P.root short) (P.root short) ≠ 0 := B.ne_zero short
    have hrel := B.pairing_mul_eq_pairing_mul_swap α k
    simp only [← P.algebraMap_pairingIn ℤ] at hrel
    rw [hα, hklen, hratio] at hrel
    have hcancel :
        algebraMap ℤ ℝ (P.pairingIn ℤ k α) =
          algebraMap ℤ ℝ (P.pairingIn ℤ α k) * (q : ℝ) := by
      apply mul_right_cancel₀ hshort
      simpa only [mul_assoc] using hrel
    have hrelInt : P.pairingIn ℤ k α = P.pairingIn ℤ α k * q := by
      apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
      push_cast
      exact hcancel
    have hpair : P.pairingIn ℤ α k ≠ 0 := pairingIn_ne_of_form_ne hkform
    rw [hrelInt, abs_mul]
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left hqabs (abs_pos.mpr hpair)
  · right
    rw [P.isShortIndex_iff]
    obtain ⟨k, hklen, hkform⟩ :=
      P.exists_form_eq_form_and_form_ne_zero B α short
    refine ⟨k, ?_⟩
    have hshort : B.form (P.root short) (P.root short) ≠ 0 := B.ne_zero short
    have hrel := B.pairing_mul_eq_pairing_mul_swap α k
    simp only [← P.algebraMap_pairingIn ℤ] at hrel
    rw [hα, hratio, hklen] at hrel
    have hcancel :
        algebraMap ℤ ℝ (P.pairingIn ℤ k α) * (q : ℝ) =
          algebraMap ℤ ℝ (P.pairingIn ℤ α k) := by
      apply mul_right_cancel₀ hshort
      simpa only [mul_assoc] using hrel
    have hrelInt : P.pairingIn ℤ k α * q = P.pairingIn ℤ α k := by
      apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
      push_cast
      exact hcancel
    have hpair : P.pairingIn ℤ k α ≠ 0 := by
      apply pairingIn_ne_of_form_ne
      have hsymm : B.form (P.root k) (P.root α) =
          B.form (P.root α) (P.root k) := by
        simpa using B.symm.eq (P.root k) (P.root α)
      exact fun hzero => hkform (hsymm.symm.trans hzero)
    rw [← hrelInt, abs_mul]
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left hqabs (abs_pos.mpr hpair)

public def _root_.RootPairing.IsPositiveRootDuality
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (ρ : Equiv.Perm ι) : Prop :=
  (∀ α, α ∈ base.support ↔ ρ α ∈ base.support) ∧
  (∀ α, base.IsPos α ↔ base.IsPos (ρ α)) ∧
  (∀ α, P.IsLongIndex α ↔ P.IsShortIndex (ρ α)) ∧
  (∀ α, P.IsShortIndex α ↔ P.IsLongIndex (ρ α)) ∧
  ∀ α β,
    P.pairingIn ℤ (ρ α) (ρ β) * P.pairingIn ℤ (ρ β) (ρ α) =
      P.pairingIn ℤ α β * P.pairingIn ℤ β α

public lemma _root_.RootPairing.isPositiveRootDuality_iff
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (ρ : Equiv.Perm ι) :
    P.IsPositiveRootDuality base ρ ↔
      (∀ α, α ∈ base.support ↔ ρ α ∈ base.support) ∧
      (∀ α, base.IsPos α ↔ base.IsPos (ρ α)) ∧
      (∀ α, P.IsLongIndex α ↔ P.IsShortIndex (ρ α)) ∧
      (∀ α, P.IsShortIndex α ↔ P.IsLongIndex (ρ α)) ∧
      ∀ α β,
        P.pairingIn ℤ (ρ α) (ρ β) * P.pairingIn ℤ (ρ β) (ρ α) =
          P.pairingIn ℤ α β * P.pairingIn ℤ β α := by
  rfl

public def IsExceptionalDualityClassification
    (classification : RootClassification) : Prop :=
  (classification.kind = .B ∧ classification.rank = 2) ∨
  (classification.kind = .F4 ∧ classification.rank = 4) ∨
  (classification.kind = .G2 ∧ classification.rank = 2)

public def ExceptionalMatrixLong {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Prop :=
  ∃ j, |A j i| > |A i j|

public lemma exceptionalMatrixLong_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    ExceptionalMatrixLong A i ↔ ∃ j, |A j i| > |A i j| := by
  rfl

public def ExceptionalMatrixShort {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Prop :=
  ∃ j, |A i j| > |A j i|

public lemma exceptionalMatrixShort_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    ExceptionalMatrixShort A i ↔ ∃ j, |A i j| > |A j i| := by
  rfl

public def ExceptionalMatrixDuality {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (p : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, ExceptionalMatrixLong A i ↔ ExceptionalMatrixShort A (p i)) ∧
  (∀ i, ExceptionalMatrixShort A i ↔ ExceptionalMatrixLong A (p i)) ∧
  ∀ i j, A (p i) (p j) * A (p j) (p i) = A i j * A j i

public lemma exceptionalMatrixDuality_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (p : Equiv.Perm (Fin n)) :
    ExceptionalMatrixDuality A p ↔
      ((∀ i, ExceptionalMatrixLong A i ↔ ExceptionalMatrixShort A (p i)) ∧
      (∀ i, ExceptionalMatrixShort A i ↔ ExceptionalMatrixLong A (p i)) ∧
      ∀ i j, A (p i) (p j) * A (p j) (p i) = A i j * A j i) := by
  rfl

public def exceptionalAbsoluteCartanFingerprint {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℤ) : Fin n → ℤ :=
  fun j => |∑ i, c i * A i j|

public lemma exceptionalAbsoluteCartanFingerprint_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℤ) (j : Fin n) :
    exceptionalAbsoluteCartanFingerprint A c j = |∑ i, c i * A i j| := by
  rfl

@[expose] public def typeB2PositiveCoeffs : Fin 4 → Fin 2 → ℤ
  | ⟨0, _⟩ => ![1, 0]
  | ⟨1, _⟩ => ![0, 1]
  | ⟨2, _⟩ => ![1, 1]
  | ⟨3, _⟩ => ![1, 2]

@[expose] public def typeG2PositiveCoeffs : Fin 6 → Fin 2 → ℤ
  | ⟨0, _⟩ => ![1, 0]
  | ⟨1, _⟩ => ![0, 1]
  | ⟨2, _⟩ => ![1, 1]
  | ⟨3, _⟩ => ![2, 1]
  | ⟨4, _⟩ => ![3, 1]
  | ⟨5, _⟩ => ![3, 2]

@[expose] public def typeF4PositiveCoeffs : Fin 24 → Fin 4 → ℤ
  | ⟨0, _⟩ => ![0, 0, 0, 1]
  | ⟨1, _⟩ => ![0, 0, 1, 0]
  | ⟨2, _⟩ => ![0, 0, 1, 1]
  | ⟨3, _⟩ => ![0, 1, 0, 0]
  | ⟨4, _⟩ => ![0, 1, 1, 0]
  | ⟨5, _⟩ => ![0, 1, 1, 1]
  | ⟨6, _⟩ => ![0, 1, 2, 0]
  | ⟨7, _⟩ => ![0, 1, 2, 1]
  | ⟨8, _⟩ => ![0, 1, 2, 2]
  | ⟨9, _⟩ => ![1, 0, 0, 0]
  | ⟨10, _⟩ => ![1, 1, 0, 0]
  | ⟨11, _⟩ => ![1, 1, 1, 0]
  | ⟨12, _⟩ => ![1, 1, 1, 1]
  | ⟨13, _⟩ => ![1, 1, 2, 0]
  | ⟨14, _⟩ => ![1, 1, 2, 1]
  | ⟨15, _⟩ => ![1, 1, 2, 2]
  | ⟨16, _⟩ => ![1, 2, 2, 0]
  | ⟨17, _⟩ => ![1, 2, 2, 1]
  | ⟨18, _⟩ => ![1, 2, 2, 2]
  | ⟨19, _⟩ => ![1, 2, 3, 1]
  | ⟨20, _⟩ => ![1, 2, 3, 2]
  | ⟨21, _⟩ => ![1, 2, 4, 2]
  | ⟨22, _⟩ => ![1, 3, 4, 2]
  | ⟨23, _⟩ => ![2, 3, 4, 2]
  | _ => ![2, 3, 4, 2]

set_option maxHeartbeats 800000 in
public lemma typeB2_positive_fingerprint_injective :
    ∀ i j : Fin 4,
      (∀ k, exceptionalAbsoluteCartanFingerprint (typeBCartanMatrix 0)
        (typeB2PositiveCoeffs i) k =
        exceptionalAbsoluteCartanFingerprint (typeBCartanMatrix 0)
          (typeB2PositiveCoeffs j) k) → i = j := by
  decide

set_option maxHeartbeats 800000 in
public lemma typeF4_positive_fingerprint_injective :
    ∀ i j : Fin 24,
      (∀ k, exceptionalAbsoluteCartanFingerprint typeF4CartanMatrix
        (typeF4PositiveCoeffs i) k =
        exceptionalAbsoluteCartanFingerprint typeF4CartanMatrix
          (typeF4PositiveCoeffs j) k) → i = j := by
  decide

set_option maxHeartbeats 800000 in
public lemma typeG2_positive_fingerprint_injective :
    ∀ i j : Fin 6,
      (∀ k, exceptionalAbsoluteCartanFingerprint typeG2CartanMatrix
        (typeG2PositiveCoeffs i) k =
        exceptionalAbsoluteCartanFingerprint typeG2CartanMatrix
          (typeG2PositiveCoeffs j) k) → i = j := by
  decide

public noncomputable def supportPerm
    {ι M N : Type*} {n : ℕ} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (numbering : base.support ≃ Fin n)
    (ρ : Equiv.Perm ι)
    (hsupport : ∀ α, α ∈ base.support ↔ ρ α ∈ base.support) :
    Equiv.Perm (Fin n) := by
  let q : base.support → base.support := fun x =>
    ⟨ρ x, (hsupport x).mp x.property⟩
  have hq : Function.Bijective q := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply ρ.injective
      exact congrArg Subtype.val hxy
    · intro y
      refine ⟨⟨ρ.symm y, (hsupport (ρ.symm y)).mpr ?_⟩, ?_⟩
      · rw [ρ.apply_symm_apply]
        exact y.property
      · apply Subtype.ext
        dsimp [q]
        exact ρ.apply_symm_apply y
  exact numbering.symm.trans ((Equiv.ofBijective q hq).trans numbering)

public lemma supportPerm_apply
    {ι M N : Type*} {n : ℕ} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (numbering : base.support ≃ Fin n)
    (ρ : Equiv.Perm ι)
    (hsupport : ∀ α, α ∈ base.support ↔ ρ α ∈ base.support)
    (i : Fin n) :
    numbering.symm (supportPerm base numbering ρ hsupport i) =
      ⟨ρ (numbering.symm i), (hsupport _).mp (numbering.symm i).property⟩ := by
  rw [supportPerm, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  change (Equiv.ofBijective _ _) (numbering.symm i) = _
  rfl

public lemma exceptional_matrix_duality_of_root_duality
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (base : P.Base) (numbering : base.support ≃ Fin n)
    (ρ : Equiv.Perm ι)
    (hsupport : ∀ α, α ∈ base.support ↔ ρ α ∈ base.support)
    (hLong : ∀ i, P.IsLongIndex (numbering.symm i) ↔
      ExceptionalMatrixLong A i)
    (hShort : ∀ i, P.IsShortIndex (numbering.symm i) ↔
      ExceptionalMatrixShort A i)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) = A i j)
    (hρ : P.IsPositiveRootDuality base ρ) :
    ExceptionalMatrixDuality A (supportPerm base numbering ρ hsupport) := by
  let p := supportPerm base numbering ρ hsupport
  have hp (i : Fin n) :
      numbering.symm (p i) =
        ⟨ρ (numbering.symm i), (hsupport _).mp (numbering.symm i).property⟩ := by
    exact supportPerm_apply base numbering ρ hsupport i
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [← hLong i, ← hShort (p i)]
    rw [hp]
    exact (hρ.2.2.1 (numbering.symm i))
  · intro i
    rw [← hShort i, ← hLong (p i)]
    rw [hp]
    simpa only [Subtype.coe_mk] using (hρ.2.2.2.1 (numbering.symm i))
  · intro i j
    rw [← hCartan i j, ← hCartan (p i) (p j), ← hCartan (p j) (p i),
      ← hCartan j i, hp, hp]
    simpa only [Subtype.coe_mk] using (hρ.2.2.2.2 (numbering.symm i) (numbering.symm j))

public lemma exceptional_base_perm_eq_reverse_of_matrix_check
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hcheck : ∀ p : Equiv.Perm (Fin n),
      ExceptionalMatrixDuality A p → p = Fin.revPerm)
    (base : P.Base) (numbering : base.support ≃ Fin n)
    (ρ : Equiv.Perm ι)
    (hsupport : ∀ α, α ∈ base.support ↔ ρ α ∈ base.support)
    (hLong : ∀ i, P.IsLongIndex (numbering.symm i) ↔
      ExceptionalMatrixLong A i)
    (hShort : ∀ i, P.IsShortIndex (numbering.symm i) ↔
      ExceptionalMatrixShort A i)
    (hCartan : ∀ i j, P.pairingIn ℤ (numbering.symm i) (numbering.symm j) = A i j)
    (hρ : P.IsPositiveRootDuality base ρ) :
    ∀ i : Fin n,
      numbering ⟨ρ (numbering.symm i), (hsupport _).mp (numbering.symm i).property⟩ =
        Fin.revPerm i := by
  have hp := hcheck (supportPerm base numbering ρ hsupport)
    (exceptional_matrix_duality_of_root_duality A base numbering ρ hsupport
      hLong hShort hCartan hρ)
  intro i
  have hi := congrArg numbering (supportPerm_apply base numbering ρ hsupport i)
  calc
    numbering ⟨ρ (numbering.symm i), (hsupport _).mp (numbering.symm i).property⟩ =
        supportPerm base numbering ρ hsupport i := by simpa using hi.symm
    _ = Fin.revPerm i := congrArg (fun q : Equiv.Perm (Fin n) => q i) hp

public lemma exceptional_b2_matrix_duality_unique
    (p : Equiv.Perm (Fin 2))
    (h : ExceptionalMatrixDuality (typeBCartanMatrix 0) p) :
    p = Fin.revPerm := by
  have hshortB2 : ∀ x : Fin 2,
      ExceptionalMatrixShort (typeBCartanMatrix 0) x ↔ x = 0 := by
    intro x
    fin_cases x
    · constructor
      · intro _
        rfl
      · intro _
        exact ⟨1, by
          norm_num [ExceptionalMatrixShort, typeBCartanMatrix]
          simp⟩
    · constructor
      · rintro ⟨j, hj⟩
        fin_cases j
        · norm_num [ExceptionalMatrixShort, typeBCartanMatrix, Fin.last] at hj
        · norm_num [ExceptionalMatrixShort, typeBCartanMatrix, Fin.last] at hj
      · intro hx
        have h' := congrArg Fin.val hx
        norm_num at h'
  have hlong1 : ExceptionalMatrixLong (typeBCartanMatrix 0) 1 := by
    exact ⟨0, by
      norm_num [ExceptionalMatrixLong, typeBCartanMatrix]
      simp⟩
  have hp1 : p 1 = 0 := hshortB2 (p 1) |>.mp ((h.1 1).mp hlong1)
  have hp0 : p 0 = 1 := by
    have hne : p 0 ≠ p 1 := p.injective.ne (by decide)
    generalize hp0 : p 0 = x
    fin_cases x <;> simp_all
  apply Equiv.ext
  intro z
  fin_cases z <;> simp_all [Fin.revPerm]

public lemma exceptional_f4_matrixLong_iff (x : Fin 4) :
    ExceptionalMatrixLong typeF4CartanMatrix x ↔ x = 2 := by
  fin_cases x
  · constructor
    · rintro ⟨j, hj⟩
      fin_cases j <;> norm_num [ExceptionalMatrixLong, typeF4CartanMatrix] at hj
    · intro hx
      have h := congrArg Fin.val hx
      norm_num at h
  · constructor
    · rintro ⟨j, hj⟩
      fin_cases j <;> norm_num [ExceptionalMatrixLong, typeF4CartanMatrix] at hj
    · intro hx
      have h := congrArg Fin.val hx
      norm_num at h
  · constructor
    · intro _
      rfl
    · intro _
      refine ⟨1, ?_⟩
      norm_num [ExceptionalMatrixLong, typeF4CartanMatrix]
  · constructor
    · rintro ⟨j, hj⟩
      fin_cases j <;> norm_num [ExceptionalMatrixLong, typeF4CartanMatrix] at hj
    · intro hx
      have h := congrArg Fin.val hx
      norm_num at h

public lemma exceptional_f4_matrixShort_iff (x : Fin 4) :
    ExceptionalMatrixShort typeF4CartanMatrix x ↔ x = 1 := by
  fin_cases x
  · constructor
    · rintro ⟨j, hj⟩
      fin_cases j <;> norm_num [ExceptionalMatrixShort, typeF4CartanMatrix] at hj
    · intro hx
      have h := congrArg Fin.val hx
      norm_num at h
  · constructor
    · intro _
      rfl
    · intro _
      refine ⟨2, ?_⟩
      norm_num [ExceptionalMatrixShort, typeF4CartanMatrix]
      simp
  · constructor
    · rintro ⟨j, hj⟩
      fin_cases j <;> norm_num [ExceptionalMatrixShort, typeF4CartanMatrix] at hj
    · intro hx
      have h := congrArg Fin.val hx
      norm_num at h
  · constructor
    · rintro ⟨j, hj⟩
      fin_cases j <;> norm_num [ExceptionalMatrixShort, typeF4CartanMatrix] at hj
    · intro hx
      have h := congrArg Fin.val hx
      norm_num at h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
public lemma exceptional_f4_matrix_duality_unique
    (p : Equiv.Perm (Fin 4))
    (h : ExceptionalMatrixDuality typeF4CartanMatrix p) :
    p = Fin.revPerm := by
  have hlongF4 := exceptional_f4_matrixLong_iff
  have hshortF4 := exceptional_f4_matrixShort_iff
  have hl := h.1 2
  have hs := h.2.1 1
  have hp2 : p 2 = 1 := by
    generalize hx : p 2 = x at hl ⊢
    exact hshortF4 x |>.mp (hl.mp (hlongF4 2 |>.mpr rfl))
  have hp1 : p 1 = 2 := by
    generalize hx : p 1 = x at hs ⊢
    exact hlongF4 x |>.mp (hs.mp (hshortF4 1 |>.mpr rfl))
  have hprod := h.2.2 0 1
  generalize hp0 : p 0 = x at hprod ⊢
  generalize hp3 : p 3 = y at hprod ⊢
  have h01 : p 0 ≠ p 1 := p.injective.ne (by decide)
  have h02 : p 0 ≠ p 2 := p.injective.ne (by decide)
  have h13 : p 1 ≠ p 3 := p.injective.ne (by decide)
  have h23 : p 2 ≠ p 3 := p.injective.ne (by decide)
  have h03 : p 0 ≠ p 3 := p.injective.ne (by decide)
  fin_cases x <;> fin_cases y <;>
    simp_all [typeF4CartanMatrix]
  all_goals
    apply Equiv.ext
    intro z
    fin_cases z <;> simp_all [Fin.revPerm]

public lemma exceptional_f4_reverse_matrix_duality :
    ExceptionalMatrixDuality typeF4CartanMatrix Fin.revPerm := by
  rw [exceptionalMatrixDuality_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [exceptional_f4_matrixLong_iff, exceptional_f4_matrixShort_iff]
    fin_cases i <;> simp [Fin.revPerm]
  · intro i
    rw [exceptional_f4_matrixShort_iff, exceptional_f4_matrixLong_iff]
    fin_cases i <;> simp [Fin.revPerm]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [typeF4CartanMatrix, Fin.revPerm, Fin.ext_iff]

public lemma exceptional_g2_matrix_duality_unique
    (p : Equiv.Perm (Fin 2))
    (h : ExceptionalMatrixDuality typeG2CartanMatrix p) :
    p = Fin.revPerm := by
  generalize hp0 : p 0 = x
  generalize hp1 : p 1 = y
  fin_cases x <;> fin_cases y <;>
    simp_all [ExceptionalMatrixLong, ExceptionalMatrixShort,
      ExceptionalMatrixDuality, typeG2CartanMatrix]
  all_goals
    apply Equiv.ext
    intro z
    fin_cases z <;> simp_all [Fin.revPerm]

end Theory.AlgebraicGroup
