module

public import Theory.AlgebraicGroup.RootSystems.IntegralTitsRankTwoBraid

/-!
# Integral Tits braid and cancellation coherence

For the concrete integral Tits matrices from `IntegralGeckConstruction`, the square of a
simple lift is not the identity: it is the usual torus element `h_i(-1)`.  This module records
that correction as `titsCancellation`, gives its explicit diagonal action on the Cartan and
root bases, and proves that it acts trivially by conjugation on the two simple-root operators
and their unipotent exponentials.  It also isolates a word-level insertion formula, so a
Coxeter cancellation can retain its necessary torus factor instead of being treated as an
identity deletion.  Exact rank-two braid equality then gives contextual braid transport for
Tits words, their inverse words, and the induced conjugation action on simple root operators.

The basis calculation applies the signed root-line formula for a Tits lift twice; reflection
involutivity restores the original root and leaves the product of the two root-string signs.
The conjugation calculation applies the positive/negative exchange identities twice.  To
recover commutation with the infinitesimal matrices from commutation with all integral
unipotents, the proof compares the degree-at-most-three divided-power polynomial at
parameters `-1`, `1`, and `2`; torsion-freeness of `ℤ` isolates its linear coefficient.

The alternating-word calculation is supplied by `IntegralTitsRankTwoBraid`, whose proof checks
the possible Coxeter orders `2`, `3`, `4`, and `6`.  This module packages that equality together
with the cancellation formula, matching the two constructors of a Coxeter move without
depending on the hidden implementation of `CoxeterMove`.  The construction is componentwise
and does not assume irreducibility.  Its source is the standard Tits representative relations
`n_i^2 = h_i(-1)` and the rank-two braid relations, realized here in Geck's integral lattice
model.
-/

namespace RootPairing.IntegralGeckConstruction

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- The sign by which the square of the `i`-th Tits lift acts on the `j`-th root line. -/
public def titsCancellationSign (i : b.support) (j : ι) : ℤ :=
  (-1 : ℤ) ^ P.chainBotCoeff i j *
    (-1 : ℤ) ^ P.chainBotCoeff i (P.reflectionPerm i j)

/-- The torus-sign correction left by cancelling two adjacent equal simple reflections. -/
public def titsCancellation (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  titsLift i * titsLift i

/-- The inverse word to the torus-sign correction. -/
public def titsCancellationInv (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  titsLiftInv i * titsLiftInv i

omit [P.IsReduced] [DecidableEq ι] in
/-- Every cancellation sign is an involutive unit of `ℤ`. -/
public lemma titsCancellationSign_mul_self (i : b.support) (j : ι) :
    titsCancellationSign i j * titsCancellationSign i j = 1 := by
  have hpow (n : ℕ) : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
    rw [← pow_add]
    simp [← two_mul]
  rw [titsCancellationSign]
  calc
    ((-1 : ℤ) ^ P.chainBotCoeff i j *
          (-1 : ℤ) ^ P.chainBotCoeff i (P.reflectionPerm i j)) *
        ((-1 : ℤ) ^ P.chainBotCoeff i j *
          (-1 : ℤ) ^ P.chainBotCoeff i (P.reflectionPerm i j)) =
        ((-1 : ℤ) ^ P.chainBotCoeff i j * (-1 : ℤ) ^ P.chainBotCoeff i j) *
          ((-1 : ℤ) ^ P.chainBotCoeff i (P.reflectionPerm i j) *
            (-1 : ℤ) ^ P.chainBotCoeff i (P.reflectionPerm i j)) := by ring
    _ = 1 := by rw [hpow, hpow, one_mul]

/-- The displayed inverse word is a right inverse to the cancellation correction. -/
public lemma titsCancellation_mul_inv (i : b.support) :
    titsCancellation i * titsCancellationInv i = 1 := by
  rw [titsCancellation, titsCancellationInv]
  calc
    (titsLift i * titsLift i) * (titsLiftInv i * titsLiftInv i) =
        titsLift i * (titsLift i * titsLiftInv i) * titsLiftInv i := by
      noncomm_ring
    _ = 1 := by rw [titsLift_mul_inv, Matrix.mul_one, titsLift_mul_inv]

/-- The displayed inverse word is a left inverse to the cancellation correction. -/
public lemma titsCancellation_inv_mul (i : b.support) :
    titsCancellationInv i * titsCancellation i = 1 := by
  rw [titsCancellation, titsCancellationInv]
  calc
    (titsLiftInv i * titsLiftInv i) * (titsLift i * titsLift i) =
        titsLiftInv i * (titsLiftInv i * titsLift i) * titsLift i := by
      noncomm_ring
    _ = 1 := by rw [titsLift_inv_mul, Matrix.mul_one, titsLift_inv_mul]

/-- The cancellation correction fixes every Cartan basis vector. -/
public lemma titsCancellation_mulVec_u (i j : b.support) :
    titsCancellation i *ᵥ u j = u j := by
  rw [titsCancellation, ← Matrix.mulVec_mulVec, titsLift_mulVec_u]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [titsLift_mulVec_u, titsLift_mulVec_u]
  have hii : |b.cartanMatrix i i| = 2 := by simp
  rw [hii]
  module

/-- The cancellation correction acts diagonally on root lines by its explicit torus sign. -/
public lemma titsCancellation_mulVec_v (i : b.support) (j : ι) :
    letI := P.indexNeg
    titsCancellation i *ᵥ v (b := b) j =
      titsCancellationSign i j • v (b := b) j := by
  let := P.indexNeg
  rw [titsCancellation, ← Matrix.mulVec_mulVec, titsLift_mulVec_v,
    Matrix.mulVec_smul, titsLift_mulVec_v]
  rw [P.reflectionPerm_self]
  simp [titsCancellationSign, mul_assoc]

/-- The torus-sign correction is itself an involution. -/
public lemma titsCancellation_mul_self (i : b.support) :
    titsCancellation i * titsCancellation i = 1 := by
  let := P.indexNeg
  apply Matrix.ext_of_mulVec_single
  intro x
  rw [← Matrix.mulVec_mulVec]
  rcases x with j | j
  · change titsCancellation i *ᵥ (titsCancellation i *ᵥ u j) =
      (1 : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) *ᵥ u j
    rw [titsCancellation_mulVec_u, titsCancellation_mulVec_u,
      Matrix.one_mulVec]
  · change titsCancellation i *ᵥ (titsCancellation i *ᵥ v (b := b) j) =
      (1 : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) *ᵥ v (b := b) j
    rw [titsCancellation_mulVec_v, Matrix.mulVec_smul,
      titsCancellation_mulVec_v, smul_smul, titsCancellationSign_mul_self,
      one_smul, Matrix.one_mulVec]

/-- The explicit inverse word represents the same involutive torus correction. -/
public lemma titsCancellationInv_eq_titsCancellation (i : b.support) :
    titsCancellationInv i = titsCancellation i := by
  calc
    titsCancellationInv i = titsCancellationInv i * 1 := by rw [Matrix.mul_one]
    _ = titsCancellationInv i * (titsCancellation i * titsCancellation i) := by
      rw [titsCancellation_mul_self]
    _ = (titsCancellationInv i * titsCancellation i) * titsCancellation i := by
      rw [Matrix.mul_assoc]
    _ = titsCancellation i := by rw [titsCancellation_inv_mul, Matrix.one_mul]

/-- The cancellation torus factor commutes with the positive simple-root exponential. -/
public lemma titsCancellation_mul_eUnipotent (i : b.support) (t : ℤ) :
    titsCancellation i * eUnipotent i t =
      eUnipotent i t * titsCancellation i := by
  rw [titsCancellation]
  calc
    (titsLift i * titsLift i) * eUnipotent i t =
        titsLift i * (titsLift i * eUnipotent i t) := by
      rw [Matrix.mul_assoc]
    _ = titsLift i * (fUnipotent i (-t) * titsLift i) := by
      rw [titsLift_mul_eUnipotent]
    _ = (titsLift i * fUnipotent i (-t)) * titsLift i := by
      rw [Matrix.mul_assoc]
    _ = (eUnipotent i t * titsLift i) * titsLift i := by
      rw [titsLift_mul_fUnipotent]
      simp
    _ = eUnipotent i t * (titsLift i * titsLift i) := by
      rw [Matrix.mul_assoc]

/-- The cancellation torus factor commutes with the negative simple-root exponential. -/
public lemma titsCancellation_mul_fUnipotent (i : b.support) (t : ℤ) :
    titsCancellation i * fUnipotent i t =
      fUnipotent i t * titsCancellation i := by
  rw [titsCancellation]
  calc
    (titsLift i * titsLift i) * fUnipotent i t =
        titsLift i * (titsLift i * fUnipotent i t) := by
      rw [Matrix.mul_assoc]
    _ = titsLift i * (eUnipotent i (-t) * titsLift i) := by
      rw [titsLift_mul_fUnipotent]
    _ = (titsLift i * eUnipotent i (-t)) * titsLift i := by
      rw [Matrix.mul_assoc]
    _ = (fUnipotent i t * titsLift i) * titsLift i := by
      rw [titsLift_mul_eUnipotent]
      simp
    _ = fUnipotent i t * (titsLift i * titsLift i) := by
      rw [Matrix.mul_assoc]

private lemma commute_eMatrix_of_commute_eUnipotent
    (i : b.support) (h : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
    (hU : ∀ t : ℤ, h * eUnipotent i t = eUnipotent i t * h) :
    h * eMatrix i = eMatrix i * h := by
  ext x y
  have h1 := congrFun (congrFun (hU 1) x) y
  have hm1 := congrFun (congrFun (hU (-1)) x) y
  have h2 := congrFun (congrFun (hU 2) x) y
  simp only [eUnipotent, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, eDividedPower_one] at h1 hm1 h2
  norm_num at h1 hm1 h2
  omega

private lemma commute_fMatrix_of_commute_fUnipotent
    (i : b.support) (h : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)
    (hU : ∀ t : ℤ, h * fUnipotent i t = fUnipotent i t * h) :
    h * fMatrix i = fMatrix i * h := by
  ext x y
  have h1 := congrFun (congrFun (hU 1) x) y
  have hm1 := congrFun (congrFun (hU (-1)) x) y
  have h2 := congrFun (congrFun (hU 2) x) y
  simp only [fUnipotent, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, fDividedPower_one] at h1 hm1 h2
  norm_num at h1 hm1 h2
  omega

/-- The cancellation torus factor commutes with the positive simple-root operator. -/
public lemma titsCancellation_mul_eMatrix (i : b.support) :
    titsCancellation i * eMatrix i = eMatrix i * titsCancellation i :=
  commute_eMatrix_of_commute_eUnipotent i (titsCancellation i)
    (titsCancellation_mul_eUnipotent i)

/-- The cancellation torus factor commutes with the negative simple-root operator. -/
public lemma titsCancellation_mul_fMatrix (i : b.support) :
    titsCancellation i * fMatrix i = fMatrix i * titsCancellation i :=
  commute_fMatrix_of_commute_fUnipotent i (titsCancellation i)
    (titsCancellation_mul_fUnipotent i)

/-- Cancellation induces the identity conjugation on the positive simple-root operator. -/
public lemma titsCancellation_conj_eMatrix (i : b.support) :
    titsCancellation i * eMatrix i * titsCancellationInv i = eMatrix i := by
  rw [titsCancellation_mul_eMatrix, Matrix.mul_assoc,
    titsCancellation_mul_inv, Matrix.mul_one]

/-- Cancellation induces the identity conjugation on the negative simple-root operator. -/
public lemma titsCancellation_conj_fMatrix (i : b.support) :
    titsCancellation i * fMatrix i * titsCancellationInv i = fMatrix i := by
  rw [titsCancellation_mul_fMatrix, Matrix.mul_assoc,
    titsCancellation_mul_inv, Matrix.mul_one]

/-- Cancellation induces the identity conjugation on the positive simple-root exponential. -/
public lemma titsCancellation_conj_eUnipotent (i : b.support) (t : ℤ) :
    titsCancellation i * eUnipotent i t * titsCancellationInv i =
      eUnipotent i t := by
  rw [titsCancellation_mul_eUnipotent, Matrix.mul_assoc,
    titsCancellation_mul_inv, Matrix.mul_one]

/-- Cancellation induces the identity conjugation on the negative simple-root exponential. -/
public lemma titsCancellation_conj_fUnipotent (i : b.support) (t : ℤ) :
    titsCancellation i * fUnipotent i t * titsCancellationInv i =
      fUnipotent i t := by
  rw [titsCancellation_mul_fUnipotent, Matrix.mul_assoc,
    titsCancellation_mul_inv, Matrix.mul_one]

omit [P.IsReduced] in
/-- Tits word evaluation carries list concatenation to matrix multiplication. -/
public lemma titsWord_append (left right : List b.support) :
    titsWord (left ++ right) = titsWord left * titsWord right := by
  induction left with
  | nil => simp [titsWord]
  | cons i left ih => simp [titsWord, ih, Matrix.mul_assoc]

omit [P.IsReduced] in
/-- In a word context, deleting an adjacent equal pair leaves its torus-sign correction. -/
public lemma titsWord_insert_cancellation (left right : List b.support) (i : b.support) :
    titsWord (left ++ i :: i :: right) =
      titsWord left * titsCancellation i * titsWord right := by
  rw [titsWord_append]
  simp [titsWord, titsCancellation, Matrix.mul_assoc]

/-- The reverse product of inverse simple lifts associated to a word. -/
@[expose] public def titsWordInv : List b.support →
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ
  | [] => 1
  | i :: word => titsWordInv word * titsLiftInv i

@[simp]
public lemma titsWordInv_nil : titsWordInv (P := P) (b := b) [] = 1 := rfl

@[simp]
public lemma titsWordInv_cons (i : b.support) (word : List b.support) :
    titsWordInv (P := P) (b := b) (i :: word) = titsWordInv word * titsLiftInv i := rfl

/-- A Tits word followed by its reverse inverse word is the identity. -/
public lemma titsWord_mul_inv (word : List b.support) :
    titsWord word * titsWordInv word = 1 := by
  induction word with
  | nil => simp [titsWord, titsWordInv]
  | cons i word ih =>
      simp only [titsWord, titsWordInv]
      calc
        (titsLift i * titsWord word) * (titsWordInv word * titsLiftInv i) =
            titsLift i * (titsWord word * titsWordInv word) * titsLiftInv i := by
          noncomm_ring
        _ = 1 := by rw [ih, Matrix.mul_one, titsLift_mul_inv]

/-- A reverse inverse Tits word followed by its Tits word is the identity. -/
public lemma titsWord_inv_mul (word : List b.support) :
    titsWordInv word * titsWord word = 1 := by
  induction word with
  | nil => simp [titsWord, titsWordInv]
  | cons i word ih =>
      simp only [titsWord, titsWordInv]
      calc
        (titsWordInv word * titsLiftInv i) * (titsLift i * titsWord word) =
            titsWordInv word * (titsLiftInv i * titsLift i) * titsWord word := by
          noncomm_ring
        _ = 1 := by rw [titsLift_inv_mul, Matrix.mul_one, ih]

/-- Equal Tits words have equal reverse inverse words. -/
public lemma titsWordInv_eq_of_titsWord_eq {word word' : List b.support}
    (h : titsWord word = titsWord word') :
    titsWordInv word = titsWordInv word' := by
  calc
    titsWordInv word = titsWordInv word * 1 := by rw [Matrix.mul_one]
    _ = titsWordInv word * (titsWord word' * titsWordInv word') := by
      rw [titsWord_mul_inv]
    _ = (titsWordInv word * titsWord word) * titsWordInv word' := by
      rw [h, Matrix.mul_assoc]
    _ = titsWordInv word' := by rw [titsWord_inv_mul, Matrix.one_mul]

/-- Conjugation by a concrete integral Tits word. -/
@[expose] public def titsConjugate (word : List b.support)
    (x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  titsWord word * x * titsWordInv word

public lemma titsConjugate_apply (word : List b.support)
    (x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    titsConjugate word x = titsWord word * x * titsWordInv word := rfl

/-- Concrete Tits-word equality induces equality of the associated conjugations. -/
public lemma titsConjugate_eq_of_titsWord_eq {word word' : List b.support}
    (h : titsWord word = titsWord word')
    (x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    titsConjugate word x = titsConjugate word' x := by
  rw [titsConjugate, titsConjugate, h, titsWordInv_eq_of_titsWord_eq h]

section RankTwoBraid

variable {κ K V W : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {Q : RootPairing κ K V W} [Q.IsCrystallographic] [Q.IsReduced]
  {c : Q.Base} [Fintype κ] [DecidableEq κ]

/-- Replacing an alternating rank-two subword by its braid mate preserves the concrete
integral Tits matrix, in an arbitrary word context. -/
public lemma titsWord_insert_braid
    (C : CoxeterMatrix c.support)
    (hC : ∀ i j : c.support,
      C i j = orderOf (c.simpleReflection i * c.simpleReflection j))
    (left right : List c.support) (i j : c.support) :
    titsWord (left ++ CoxeterSystem.braidWord C i j ++ right) =
      titsWord (left ++ CoxeterSystem.braidWord C j i ++ right) := by
  simpa only [titsWord_append, Matrix.mul_assoc] using congrArg
    (fun middle => titsWord left * middle * titsWord right)
    (titsWord_braidWord_eq_of_orders (P := Q) (b := c) C hC i j)

/-- Contextual braid replacement also preserves the reverse inverse Tits word. -/
public lemma titsWordInv_insert_braid
    (C : CoxeterMatrix c.support)
    (hC : ∀ i j : c.support,
      C i j = orderOf (c.simpleReflection i * c.simpleReflection j))
    (left right : List c.support) (i j : c.support) :
    titsWordInv (left ++ CoxeterSystem.braidWord C i j ++ right) =
      titsWordInv (left ++ CoxeterSystem.braidWord C j i ++ right) :=
  titsWordInv_eq_of_titsWord_eq (titsWord_insert_braid C hC left right i j)

/-- Contextual braid replacement preserves conjugation by a concrete Tits word. -/
public lemma titsConjugate_insert_braid
    (C : CoxeterMatrix c.support)
    (hC : ∀ i j : c.support,
      C i j = orderOf (c.simpleReflection i * c.simpleReflection j))
    (left right : List c.support) (i j : c.support)
    (x : Matrix (c.support ⊕ κ) (c.support ⊕ κ) ℤ) :
    titsConjugate (left ++ CoxeterSystem.braidWord C i j ++ right) x =
      titsConjugate (left ++ CoxeterSystem.braidWord C j i ++ right) x :=
  titsConjugate_eq_of_titsWord_eq (titsWord_insert_braid C hC left right i j) x

/-- Contextual braid replacement preserves conjugation of a positive simple-root operator. -/
public lemma titsConjugate_insert_braid_eMatrix
    (C : CoxeterMatrix c.support)
    (hC : ∀ i j : c.support,
      C i j = orderOf (c.simpleReflection i * c.simpleReflection j))
    (left right : List c.support) (i j k : c.support) :
    titsConjugate (left ++ CoxeterSystem.braidWord C i j ++ right) (eMatrix k) =
      titsConjugate (left ++ CoxeterSystem.braidWord C j i ++ right) (eMatrix k) :=
  titsConjugate_insert_braid C hC left right i j (eMatrix k)

/-- Contextual braid replacement preserves conjugation of a negative simple-root operator. -/
public lemma titsConjugate_insert_braid_fMatrix
    (C : CoxeterMatrix c.support)
    (hC : ∀ i j : c.support,
      C i j = orderOf (c.simpleReflection i * c.simpleReflection j))
    (left right : List c.support) (i j k : c.support) :
    titsConjugate (left ++ CoxeterSystem.braidWord C i j ++ right) (fMatrix k) =
      titsConjugate (left ++ CoxeterSystem.braidWord C j i ++ right) (fMatrix k) :=
  titsConjugate_insert_braid C hC left right i j (fMatrix k)

end RankTwoBraid

end
end RootPairing.IntegralGeckConstruction
