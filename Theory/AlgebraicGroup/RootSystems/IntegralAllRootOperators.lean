module

public import Theory.AlgebraicGroup.RootSystems.IntegralTitsCoherence
public import Theory.AlgebraicGroup.RootSystems.Matsumoto
public import Theory.AlgebraicGroup.RootSystems.PositiveSubsystem

/-!
# Integral operators on every root line

For a finite reduced crystallographic root pairing and a chosen base, this module extends
Geck's integral simple-root operators to every root without an irreducibility hypothesis.
For each positive root it chooses a reduced Weyl word carrying a simple root to that root;
the negative operator is transported along the same word.  Thus opposite roots share one
rank-one normalization rather than making unrelated choices.

The Tits-word transport is independent of the reduced spelling of a fixed Weyl element.
Indeed, Matsumoto connectivity expresses two reduced words by Coxeter moves.  A cancellation
move would strictly lower the length and is therefore impossible along a reduced chain, while
the contextual rank-two braid equality from `IntegralTitsCoherence` identifies each remaining
move integrally.  Conjugation by the resulting Tits matrix transports simple root-string
actions to arbitrary root lines.

The transported operators retain Geck's divided-power multiplication and factorial formulas,
uniform fourth-power nilpotence, and additive one-parameter unipotent law.  Explicit formulas
record the positive and negative root-string actions and the normalized opposite-root
three-dimensional string.  The construction is componentwise, so reducible pairings require
no decomposition into irreducible factors.  Its mathematical sources are Geck's integral
root-string construction and the standard Matsumoto-Tits braid presentation.
-/

namespace RootPairing.IntegralGeckConstruction

open Matrix
open Theory.AlgebraicGroup

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

lemma root_reflectionWord (word : List b.support) (i : ι) :
    P.root (reflectionWord word i) = b.wordProd word • P.root i := by
  induction word with
  | nil => simp [reflectionWord, b.wordProd_nil]
  | cons j word ih =>
      rw [reflectionWord, P.root_reflectionPerm, ih, b.wordProd_cons,
        mul_smul]
      rfl

lemma reflectionWord_eq_weylGroupToPerm (word : List b.support) (i : ι) :
    reflectionWord word i = P.weylGroupToPerm (b.wordProd word) i := by
  apply P.root.injective
  rw [root_reflectionWord, P.weylGroup_apply_root]

lemma reflectionWord_neg (word : List b.support) (i : ι) :
    letI := P.indexNeg
    reflectionWord word (-i) = -reflectionWord word i := by
  let := P.indexNeg
  rw [reflectionWord_eq_weylGroupToPerm,
    P.weylGroupToPerm_neg, reflectionWord_eq_weylGroupToPerm]

/-- A reduced simple-root route whose Weyl word carries its source to `i`. -/
structure RootRoute (i : ι) where
  simple : b.support
  word : List b.support
  reduced : word.length = b.wordLength (b.wordProd word)
  target : reflectionWord word simple = i

lemma rootRoute_exists (i : ι) : Nonempty (RootRoute (P := P) (b := b) i) := by
  obtain ⟨g, j, hj, hg⟩ :=
    Theory.AlgebraicGroup.weylGroup_orbit_meets_base P b i
  obtain ⟨word, hlen, hword⟩ := b.wordLength_spec g⁻¹
  let simple : b.support := ⟨j, hj⟩
  refine ⟨simple, word, ?_, ?_⟩
  · rw [hword]
    exact hlen
  · apply P.root.injective
    rw [root_reflectionWord, hword]
    change g⁻¹ • P.root j = P.root i
    rw [← hg]
    simp

/-- The canonical chosen reduced route to a root, with the empty route used on simple roots. -/
def rootRoute (i : ι) : RootRoute (P := P) (b := b) i :=
  if hi : i ∈ b.support then
    { simple := ⟨i, hi⟩
      word := []
      reduced := by simp
      target := by simp [reflectionWord] }
  else Classical.choice (rootRoute_exists (P := P) (b := b) i)

@[simp] lemma rootRoute_simple (i : b.support) :
    (rootRoute (P := P) (b := b) i).simple = i := by
  simp [rootRoute, i.property]

@[simp] lemma rootRoute_word_simple (i : b.support) :
    (rootRoute (P := P) (b := b) i).word = [] := by
  simp [rootRoute, i.property]

/-- Transport a carrier vector by the integral Tits matrix of a word. -/
def transportedVector (word : List b.support) (x : Carrier (b := b)) : Carrier (b := b) :=
  titsWord word *ᵥ x

/-- Conjugate an integral endomorphism by the Tits matrix of a word. -/
def transportedMatrix (word : List b.support)
    (x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  titsWord word * x * titsWordInv word

lemma transportedVector_add (word : List b.support) (x y : Carrier (b := b)) :
    transportedVector word (x + y) =
      transportedVector word x + transportedVector word y := by
  simp [transportedVector, Matrix.mulVec_add]

lemma transportedVector_smul (word : List b.support) (t : ℤ)
    (x : Carrier (b := b)) :
    transportedVector word (t • x) = t • transportedVector word x := by
  exact Matrix.mulVec_smul (R := ℤ) (titsWord word) t x

lemma transportedMatrix_mulVec_transport (word : List b.support)
    (x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) (y : Carrier (b := b)) :
    transportedMatrix word x *ᵥ transportedVector word y =
      transportedVector word (x *ᵥ y) := by
  change (titsWord word * x * titsWordInv word) *ᵥ
      (titsWord word *ᵥ y) = titsWord word *ᵥ (x *ᵥ y)
  calc
    (titsWord word * x * titsWordInv word) *ᵥ (titsWord word *ᵥ y) =
        ((titsWord word * x * titsWordInv word) * titsWord word) *ᵥ y := by
          rw [Matrix.mulVec_mulVec]
    _ = (titsWord word * x) *ᵥ y := by
      rw [show (titsWord word * x * titsWordInv word) * titsWord word =
        titsWord word * x * (titsWordInv word * titsWord word) by noncomm_ring,
        titsWord_inv_mul, Matrix.mul_one]
    _ = titsWord word *ᵥ (x *ᵥ y) := (Matrix.mulVec_mulVec _ _ _).symm

/-- The integral infinitesimal operator indexed by any root. -/
def rootOperator (i : ι) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  by
    classical
    letI := P.indexNeg
    exact if hi : b.IsPos i then
      transportedMatrix (rootRoute (P := P) (b := b) i).word
        (eMatrix (rootRoute (P := P) (b := b) i).simple)
    else
      transportedMatrix (rootRoute (P := P) (b := b) (-i)).word
        (fMatrix (rootRoute (P := P) (b := b) (-i)).simple)

/-- The `n`-th integral divided power of the operator on root `i`. -/
def rootDividedPower (i : ι) (n : ℕ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  by
    classical
    letI := P.indexNeg
    exact if hi : b.IsPos i then
      transportedMatrix (rootRoute (P := P) (b := b) i).word
        (eDividedPower (rootRoute (P := P) (b := b) i).simple n)
    else
      transportedMatrix (rootRoute (P := P) (b := b) (-i)).word
        (fDividedPower (rootRoute (P := P) (b := b) (-i)).simple n)

/-- The integral divided-power exponential on root `i` at parameter `t`. -/
def rootUnipotent (i : ι) (t : ℤ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  by
    classical
    letI := P.indexNeg
    exact if hi : b.IsPos i then
      transportedMatrix (rootRoute (P := P) (b := b) i).word
        (eUnipotent (rootRoute (P := P) (b := b) i).simple t)
    else
      transportedMatrix (rootRoute (P := P) (b := b) (-i)).word
        (fUnipotent (rootRoute (P := P) (b := b) (-i)).simple t)

/-- The normalized transported basis vector on the line indexed by root `i`. -/
def rootVector (i : ι) : Carrier (b := b) :=
  by
    classical
    letI := P.indexNeg
    exact if hi : b.IsPos i then
      transportedVector (rootRoute (P := P) (b := b) i).word
        (v (b := b) (rootRoute (P := P) (b := b) i).simple)
    else
      transportedVector (rootRoute (P := P) (b := b) (-i)).word
        (v (b := b) (-(rootRoute (P := P) (b := b) (-i)).simple : ι))

/-- The Cartan vector transported along the chosen route to `i`. -/
def rootCartanVector (i : ι) : Carrier (b := b) :=
  transportedVector (rootRoute (P := P) (b := b) i).word
    (u (rootRoute (P := P) (b := b) i).simple)

lemma transportedMatrix_one (word : List b.support) :
    transportedMatrix (P := P) word 1 = 1 := by
  simp [transportedMatrix, titsWord_mul_inv]

lemma transportedMatrix_zero (word : List b.support) :
    transportedMatrix (P := P) word 0 = 0 := by
  simp [transportedMatrix]

lemma transportedMatrix_add (word : List b.support)
    (x y : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    transportedMatrix word (x + y) =
      transportedMatrix word x + transportedMatrix word y := by
  simp [transportedMatrix, Matrix.mul_add, Matrix.add_mul]

lemma transportedMatrix_smul (word : List b.support) (n : ℕ)
    (x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    transportedMatrix word (n • x) = n • transportedMatrix word x := by
  induction n with
  | zero => simp [transportedMatrix_zero]
  | succ n ih =>
      rw [succ_nsmul, transportedMatrix_add, ih, succ_nsmul]

lemma transportedMatrix_mul (word : List b.support)
    (x y : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    transportedMatrix word (x * y) =
      transportedMatrix word x * transportedMatrix word y := by
  simp only [transportedMatrix]
  rw [show (titsWord word * x * titsWordInv word) *
      (titsWord word * y * titsWordInv word) =
      titsWord word * x * (titsWordInv word * titsWord word) * y *
        titsWordInv word by noncomm_ring,
    titsWord_inv_mul, Matrix.mul_one]
  noncomm_ring

lemma transportedMatrix_pow (word : List b.support)
    (x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) (n : ℕ) :
    transportedMatrix word (x ^ n) = transportedMatrix word x ^ n := by
  induction n with
  | zero => simp [transportedMatrix_one]
  | succ n ih =>
      rw [pow_succ, pow_succ, transportedMatrix_mul, ih]

private lemma titsWord_eq_of_coxeterMove_of_reduced
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {source result : List b.support}
    (hred : source.length = b.wordLength (b.wordProd source))
    (hmove : Theory.AlgebraicGroup.CoxeterMove C source result) :
    titsWord source = titsWord result ∧
      result.length = b.wordLength (b.wordProd result) := by
  rcases hmove with hcancel | hbraid
  · rcases hcancel with ⟨left, right, i, rfl, rfl⟩
    have hprod : b.wordProd (left ++ [i, i] ++ right) =
        b.wordProd (left ++ right) := by
      simp only [b.wordProd_append, b.wordProd_cons, b.wordProd_nil,
        mul_one]
      rw [mul_assoc, b.simpleReflection_mul_self, one_mul]
    have hle := b.wordLength_le (b.wordProd (left ++ right))
      (left ++ right) rfl
    rw [hprod] at hred
    simp only [List.length_append, List.length_cons, List.length_nil] at hred hle
    omega
  · rcases hbraid with ⟨left, right, i, j, rfl, rfl⟩
    have hprod :
        b.wordProd (left ++ CoxeterSystem.braidWord C i j ++ right) =
          b.wordProd (left ++ CoxeterSystem.braidWord C j i ++ right) := by
      simp only [b.wordProd_append]
      rw [b.wordProd_braidWord_eq_of_orders C hC i j]
    have hlen :
        (left ++ CoxeterSystem.braidWord C i j ++ right).length =
          (left ++ CoxeterSystem.braidWord C j i ++ right).length := by
      simp only [List.length_append, CoxeterSystem.length_alternatingWord]
      rw [C.symmetric]
    constructor
    · exact titsWord_insert_braid C hC left right i j
    · calc
        (left ++ CoxeterSystem.braidWord C j i ++ right).length =
            (left ++ CoxeterSystem.braidWord C i j ++ right).length := hlen.symm
        _ = b.wordLength
            (b.wordProd (left ++ CoxeterSystem.braidWord C i j ++ right)) := hred
        _ = b.wordLength
            (b.wordProd (left ++ CoxeterSystem.braidWord C j i ++ right)) := by
              rw [hprod]

lemma titsWord_eq_of_reducedWords
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {word word' : List b.support}
    (hprod : b.wordProd word = b.wordProd word')
    (hred : word.length = b.wordLength (b.wordProd word))
    (hred' : word'.length = b.wordLength (b.wordProd word')) :
    titsWord word = titsWord word' := by
  have moves := b.reducedWords_reflTransGen_coxeterMove
    C hC word word' hprod hred hred'
  have aux : ∀ {source result : List b.support},
      Relation.ReflTransGen (Theory.AlgebraicGroup.CoxeterMove C) source result →
      source.length = b.wordLength (b.wordProd source) →
      titsWord source = titsWord result ∧
        result.length = b.wordLength (b.wordProd result) := by
    intro source result path
    induction path with
    | refl =>
        intro hsource
        exact ⟨rfl, hsource⟩
    | tail path hmove ih =>
        intro hsource
        obtain ⟨hword, hmiddle⟩ := ih hsource
        obtain ⟨hstep, hresult⟩ :=
          titsWord_eq_of_coxeterMove_of_reduced C hC hmiddle hmove
        exact ⟨hword.trans hstep, hresult⟩
  exact (aux moves hred).1

lemma transportedVector_eq_of_reducedWords
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {word word' : List b.support}
    (hprod : b.wordProd word = b.wordProd word')
    (hred : word.length = b.wordLength (b.wordProd word))
    (hred' : word'.length = b.wordLength (b.wordProd word'))
    (x : Carrier (b := b)) :
    transportedVector word x = transportedVector word' x := by
  rw [transportedVector, transportedVector,
    titsWord_eq_of_reducedWords C hC hprod hred hred']

lemma transportedMatrix_eq_of_reducedWords
    (C : CoxeterMatrix b.support)
    (hC : ∀ i j : b.support,
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j))
    {word word' : List b.support}
    (hprod : b.wordProd word = b.wordProd word')
    (hred : word.length = b.wordLength (b.wordProd word))
    (hred' : word'.length = b.wordLength (b.wordProd word'))
    (x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    transportedMatrix word x = transportedMatrix word' x := by
  have hword := titsWord_eq_of_reducedWords C hC hprod hred hred'
  rw [transportedMatrix, transportedMatrix, hword,
    titsWordInv_eq_of_titsWord_eq hword]

@[simp] lemma transportedMatrix_nil
    (x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    transportedMatrix (P := P) [] x = x := by
  have hinv : titsWordInv (P := P) (b := b) [] = 1 := by
    simp [titsWord]
  simp [transportedMatrix, titsWord, hinv]

private lemma reflectionPerm_self_twice (i : ι) :
    P.reflectionPerm (P.reflectionPerm i i) (P.reflectionPerm i i) = i := by
  apply P.root.injective
  rw [P.root_reflectionPerm, P.reflection_apply_self,
    P.root_reflectionPerm, P.reflection_apply_self]
  simp

lemma rootOperator_of_pos (i : ι) (hi : b.IsPos i) :
    rootOperator (P := P) (b := b) i =
      transportedMatrix (rootRoute (P := P) (b := b) i).word
        (eMatrix (rootRoute (P := P) (b := b) i).simple) := by
  simp [rootOperator, hi]

lemma rootOperator_neg_of_pos (i : ι) (hi : b.IsPos i) :
    letI := P.indexNeg
    rootOperator (P := P) (b := b) (-i) =
      transportedMatrix (rootRoute (P := P) (b := b) i).word
        (fMatrix (rootRoute (P := P) (b := b) i).simple) := by
  let := P.indexNeg
  have hneg : ¬b.IsPos (-i) := by
    rw [RootPairing.Base.IsPos.neg_iff_not]
    exact not_not_intro hi
  rw [rootOperator, dif_neg hneg]
  simp only [indexNeg_neg]
  rw [reflectionPerm_self_twice]

lemma rootDividedPower_of_pos (i : ι) (hi : b.IsPos i) (n : ℕ) :
    rootDividedPower (P := P) (b := b) i n =
      transportedMatrix (rootRoute (P := P) (b := b) i).word
        (eDividedPower (rootRoute (P := P) (b := b) i).simple n) := by
  simp [rootDividedPower, hi]

lemma rootDividedPower_neg_of_pos (i : ι) (hi : b.IsPos i) (n : ℕ) :
    letI := P.indexNeg
    rootDividedPower (P := P) (b := b) (-i) n =
      transportedMatrix (rootRoute (P := P) (b := b) i).word
        (fDividedPower (rootRoute (P := P) (b := b) i).simple n) := by
  let := P.indexNeg
  have hneg : ¬b.IsPos (-i) := by
    rw [RootPairing.Base.IsPos.neg_iff_not]
    exact not_not_intro hi
  rw [rootDividedPower, dif_neg hneg]
  simp only [indexNeg_neg]
  rw [reflectionPerm_self_twice]

lemma rootUnipotent_of_pos (i : ι) (hi : b.IsPos i) (t : ℤ) :
    rootUnipotent (P := P) (b := b) i t =
      transportedMatrix (rootRoute (P := P) (b := b) i).word
        (eUnipotent (rootRoute (P := P) (b := b) i).simple t) := by
  simp [rootUnipotent, hi]

lemma rootUnipotent_neg_of_pos (i : ι) (hi : b.IsPos i) (t : ℤ) :
    letI := P.indexNeg
    rootUnipotent (P := P) (b := b) (-i) t =
      transportedMatrix (rootRoute (P := P) (b := b) i).word
        (fUnipotent (rootRoute (P := P) (b := b) i).simple t) := by
  let := P.indexNeg
  have hneg : ¬b.IsPos (-i) := by
    rw [RootPairing.Base.IsPos.neg_iff_not]
    exact not_not_intro hi
  rw [rootUnipotent, dif_neg hneg]
  simp only [indexNeg_neg]
  rw [reflectionPerm_self_twice]

lemma rootVector_of_pos (i : ι) (hi : b.IsPos i) :
    rootVector (P := P) (b := b) i =
      transportedVector (rootRoute (P := P) (b := b) i).word
        (v (b := b) (rootRoute (P := P) (b := b) i).simple) := by
  simp [rootVector, hi]

lemma rootVector_neg_of_pos (i : ι) (hi : b.IsPos i) :
    letI := P.indexNeg
    rootVector (P := P) (b := b) (-i) =
      transportedVector (rootRoute (P := P) (b := b) i).word
        (v (b := b) (-(rootRoute (P := P) (b := b) i).simple : ι)) := by
  let := P.indexNeg
  have hneg : ¬b.IsPos (-i) := by
    rw [RootPairing.Base.IsPos.neg_iff_not]
    exact not_not_intro hi
  rw [rootVector, dif_neg hneg]
  simp only [indexNeg_neg]
  rw [reflectionPerm_self_twice]

@[simp] lemma rootDividedPower_zero (i : ι) :
    rootDividedPower (P := P) (b := b) i 0 = 1 := by
  classical
  letI := P.indexNeg
  by_cases hi : b.IsPos i <;>
    simp [rootDividedPower, hi, transportedMatrix_one]

@[simp] lemma rootDividedPower_one (i : ι) :
    rootDividedPower (P := P) (b := b) i 1 = rootOperator i := by
  classical
  letI := P.indexNeg
  by_cases hi : b.IsPos i <;>
    simp [rootDividedPower, rootOperator, hi]

lemma rootDividedPower_mul (i : ι) (m n : ℕ) :
    rootDividedPower (P := P) (b := b) i m * rootDividedPower i n =
      (m + n).choose m • rootDividedPower i (m + n) := by
  classical
  letI := P.indexNeg
  by_cases hi : b.IsPos i
  · simp only [rootDividedPower, dif_pos hi]
    rw [← transportedMatrix_mul, eDividedPower_mul,
      transportedMatrix_smul]
  · simp only [rootDividedPower, dif_neg hi]
    rw [← transportedMatrix_mul, fDividedPower_mul,
      transportedMatrix_smul]

lemma rootOperator_pow_eq_factorial_smul (i : ι) (n : ℕ) :
    rootOperator (P := P) (b := b) i ^ n =
      n.factorial • rootDividedPower i n := by
  classical
  letI := P.indexNeg
  by_cases hi : b.IsPos i
  · simp only [rootOperator, rootDividedPower, dif_pos hi]
    rw [← transportedMatrix_pow, eMatrix_pow_eq_factorial_smul,
      transportedMatrix_smul]
  · simp only [rootOperator, rootDividedPower, dif_neg hi]
    rw [← transportedMatrix_pow, fMatrix_pow_eq_factorial_smul,
      transportedMatrix_smul]

lemma rootDividedPower_eq_zero_of_four_le (i : ι) {n : ℕ} (hn : 4 ≤ n) :
    rootDividedPower (P := P) (b := b) i n = 0 := by
  classical
  letI := P.indexNeg
  by_cases hi : b.IsPos i
  · simp only [rootDividedPower, dif_pos hi]
    rw [eDividedPower_eq_zero_of_four_le _ hn, transportedMatrix_zero]
  · simp only [rootDividedPower, dif_neg hi]
    rw [fDividedPower_eq_zero_of_four_le _ hn, transportedMatrix_zero]

lemma rootOperator_pow_four (i : ι) :
    rootOperator (P := P) (b := b) i ^ 4 = 0 := by
  rw [rootOperator_pow_eq_factorial_smul,
    rootDividedPower_eq_zero_of_four_le i (by omega)]
  simp

@[simp] lemma rootUnipotent_zero (i : ι) :
    rootUnipotent (P := P) (b := b) i 0 = 1 := by
  classical
  letI := P.indexNeg
  by_cases hi : b.IsPos i <;>
    simp [rootUnipotent, hi, transportedMatrix_one]

lemma rootUnipotent_add (i : ι) (s t : ℤ) :
    rootUnipotent (P := P) (b := b) i s * rootUnipotent i t =
      rootUnipotent i (s + t) := by
  classical
  letI := P.indexNeg
  by_cases hi : b.IsPos i
  · simp only [rootUnipotent, dif_pos hi]
    rw [← transportedMatrix_mul, eUnipotent_add]
  · simp only [rootUnipotent, dif_neg hi]
    rw [← transportedMatrix_mul, fUnipotent_add]

lemma rootUnipotent_mul_neg (i : ι) (t : ℤ) :
    rootUnipotent (P := P) (b := b) i t * rootUnipotent i (-t) = 1 := by
  rw [rootUnipotent_add]
  simp

lemma rootUnipotent_neg_mul (i : ι) (t : ℤ) :
    rootUnipotent (P := P) (b := b) i (-t) * rootUnipotent i t = 1 := by
  rw [rootUnipotent_add]
  simp

lemma rootOperator_mulVec_transport_of_pos (i : ι) (hi : b.IsPos i)
    (x : Carrier (b := b)) :
    rootOperator (P := P) (b := b) i *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word x =
      transportedVector (rootRoute (P := P) (b := b) i).word
        (eMatrix (rootRoute (P := P) (b := b) i).simple *ᵥ x) := by
  rw [rootOperator_of_pos i hi, transportedMatrix_mulVec_transport]

lemma rootOperator_neg_mulVec_transport_of_pos (i : ι) (hi : b.IsPos i)
    (x : Carrier (b := b)) :
    letI := P.indexNeg
    rootOperator (P := P) (b := b) (-i) *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word x =
      transportedVector (rootRoute (P := P) (b := b) i).word
        (fMatrix (rootRoute (P := P) (b := b) i).simple *ᵥ x) := by
  let := P.indexNeg
  rw [rootOperator_neg_of_pos i hi, transportedMatrix_mulVec_transport]

lemma rootDividedPower_mulVec_transport_of_pos (i : ι) (hi : b.IsPos i)
    (n : ℕ) (x : Carrier (b := b)) :
    rootDividedPower (P := P) (b := b) i n *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word x =
      transportedVector (rootRoute (P := P) (b := b) i).word
        (eDividedPower (rootRoute (P := P) (b := b) i).simple n *ᵥ x) := by
  rw [rootDividedPower_of_pos i hi, transportedMatrix_mulVec_transport]

lemma rootDividedPower_neg_mulVec_transport_of_pos (i : ι) (hi : b.IsPos i)
    (n : ℕ) (x : Carrier (b := b)) :
    letI := P.indexNeg
    rootDividedPower (P := P) (b := b) (-i) n *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word x =
      transportedVector (rootRoute (P := P) (b := b) i).word
        (fDividedPower (rootRoute (P := P) (b := b) i).simple n *ᵥ x) := by
  let := P.indexNeg
  rw [rootDividedPower_neg_of_pos i hi,
    transportedMatrix_mulVec_transport]

lemma rootUnipotent_mulVec_transport_of_pos (i : ι) (hi : b.IsPos i)
    (t : ℤ) (x : Carrier (b := b)) :
    rootUnipotent (P := P) (b := b) i t *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word x =
      transportedVector (rootRoute (P := P) (b := b) i).word
        (eUnipotent (rootRoute (P := P) (b := b) i).simple t *ᵥ x) := by
  rw [rootUnipotent_of_pos i hi, transportedMatrix_mulVec_transport]

lemma rootUnipotent_neg_mulVec_transport_of_pos (i : ι) (hi : b.IsPos i)
    (t : ℤ) (x : Carrier (b := b)) :
    letI := P.indexNeg
    rootUnipotent (P := P) (b := b) (-i) t *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word x =
      transportedVector (rootRoute (P := P) (b := b) i).word
        (fUnipotent (rootRoute (P := P) (b := b) i).simple t *ᵥ x) := by
  let := P.indexNeg
  rw [rootUnipotent_neg_of_pos i hi, transportedMatrix_mulVec_transport]

lemma rootOperator_mulVec_root_add_of_pos (i : ι) (hi : b.IsPos i)
    {j k : ι}
    (h : P.root k =
      P.root (rootRoute (P := P) (b := b) i).simple + P.root j) :
    rootOperator (P := P) (b := b) i *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word (v (b := b) j) =
      (P.chainBotCoeff (rootRoute (P := P) (b := b) i).simple j + 1 : ℤ) •
        transportedVector (rootRoute (P := P) (b := b) i).word (v (b := b) k) := by
  rw [rootOperator_mulVec_transport_of_pos i hi,
    eMatrix_mulVec_v_add h, transportedVector_smul]

lemma rootOperator_neg_mulVec_root_sub_of_pos (i : ι) (hi : b.IsPos i)
    {j k : ι}
    (h : P.root k =
      P.root j - P.root (rootRoute (P := P) (b := b) i).simple) :
    letI := P.indexNeg
    rootOperator (P := P) (b := b) (-i) *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word (v (b := b) j) =
      (P.chainTopCoeff (rootRoute (P := P) (b := b) i).simple j + 1 : ℤ) •
        transportedVector (rootRoute (P := P) (b := b) i).word (v (b := b) k) := by
  let := P.indexNeg
  rw [rootOperator_neg_mulVec_transport_of_pos i hi,
    fMatrix_mulVec_v_sub h, transportedVector_smul]

lemma rootDividedPower_add_two_mulVec_root_add_of_pos
    (i : ι) (hi : b.IsPos i) (n : ℕ) {j k : ι}
    (h : P.root k = P.root j +
      (n + 2) • P.root (rootRoute (P := P) (b := b) i).simple) :
    rootDividedPower (P := P) (b := b) i (n + 2) *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word (v (b := b) j) =
      ((P.chainBotCoeff (rootRoute (P := P) (b := b) i).simple j + n + 2).choose
          (n + 2) : ℤ) •
        transportedVector (rootRoute (P := P) (b := b) i).word (v (b := b) k) := by
  rw [rootDividedPower_mulVec_transport_of_pos i hi,
    eDividedPower_add_two_mulVec_v n h, transportedVector_smul]

lemma rootDividedPower_neg_add_two_mulVec_root_sub_of_pos
    (i : ι) (hi : b.IsPos i) (n : ℕ) {j k : ι}
    (h : P.root k = P.root j -
      (n + 2) • P.root (rootRoute (P := P) (b := b) i).simple) :
    letI := P.indexNeg
    rootDividedPower (P := P) (b := b) (-i) (n + 2) *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word (v (b := b) j) =
      ((P.chainTopCoeff (rootRoute (P := P) (b := b) i).simple j + n + 2).choose
          (n + 2) : ℤ) •
        transportedVector (rootRoute (P := P) (b := b) i).word (v (b := b) k) := by
  let := P.indexNeg
  rw [rootDividedPower_neg_mulVec_transport_of_pos i hi,
    fDividedPower_add_two_mulVec_v n h, transportedVector_smul]

lemma rootVector_of_pos_eq_smul_v (i : ι) (hi : b.IsPos i) :
    rootVector (P := P) (b := b) i =
      titsWordSign (rootRoute (P := P) (b := b) i).word
          (rootRoute (P := P) (b := b) i).simple • v (b := b) i := by
  rw [rootVector_of_pos i hi]
  rw [transportedVector, titsWord_mulVec_v,
    (rootRoute (P := P) (b := b) i).target]

lemma rootVector_neg_of_pos_eq_smul_v (i : ι) (hi : b.IsPos i) :
    letI := P.indexNeg
    rootVector (P := P) (b := b) (-i) =
      titsWordSign (rootRoute (P := P) (b := b) i).word
          (-(rootRoute (P := P) (b := b) i).simple : ι) • v (b := b) (-i) := by
  let := P.indexNeg
  rw [rootVector_neg_of_pos i hi]
  simp only [transportedVector, titsWord_mulVec_v]
  rw [reflectionWord_neg, (rootRoute (P := P) (b := b) i).target]

@[simp] lemma rootOperator_simple (i : b.support) :
    rootOperator (P := P) (b := b) i = eMatrix i := by
  rw [rootOperator_of_pos (i : ι) (b.isPos_of_mem_support i.property)]
  simp

@[simp] lemma rootOperator_neg_simple (i : b.support) :
    letI := P.indexNeg
    rootOperator (P := P) (b := b) (-i) = fMatrix i := by
  let := P.indexNeg
  rw [rootOperator_neg_of_pos (i : ι) (b.isPos_of_mem_support i.property)]
  simp

lemma rootOperator_mulVec_opposite (i : ι) (hi : b.IsPos i) :
    letI := P.indexNeg
    rootOperator (P := P) (b := b) i *ᵥ rootVector (P := P) (b := b) (-i) =
      rootCartanVector (P := P) (b := b) i := by
  let := P.indexNeg
  rw [rootOperator_of_pos i hi, rootVector_neg_of_pos i hi,
    transportedMatrix_mulVec_transport,
    eMatrix_mulVec_v_neg]
  rfl

lemma rootOperator_neg_mulVec (i : ι) (hi : b.IsPos i) :
    letI := P.indexNeg
    rootOperator (P := P) (b := b) (-i) *ᵥ rootVector (P := P) (b := b) i =
      rootCartanVector (P := P) (b := b) i := by
  let := P.indexNeg
  rw [rootOperator_neg_of_pos i hi, rootVector_of_pos i hi,
    transportedMatrix_mulVec_transport,
    fMatrix_mulVec_v_same]
  rfl

lemma rootUnipotent_mulVec_opposite (i : ι) (hi : b.IsPos i) (t : ℤ) :
    letI := P.indexNeg
    rootUnipotent (P := P) (b := b) i t *ᵥ rootVector (P := P) (b := b) (-i) =
      rootVector (P := P) (b := b) (-i) +
        t • rootCartanVector (P := P) (b := b) i +
          t ^ 2 • rootVector (P := P) (b := b) i := by
  let := P.indexNeg
  rw [rootVector_neg_of_pos i hi, rootVector_of_pos i hi,
    rootUnipotent_mulVec_transport_of_pos i hi,
    eUnipotent_mulVec_v_neg,
    transportedVector_add, transportedVector_add,
    transportedVector_smul, transportedVector_smul]
  rfl

lemma rootUnipotent_neg_mulVec_same (i : ι) (hi : b.IsPos i) (t : ℤ) :
    letI := P.indexNeg
    rootUnipotent (P := P) (b := b) (-i) t *ᵥ rootVector (P := P) (b := b) i =
      rootVector (P := P) (b := b) i +
        t • rootCartanVector (P := P) (b := b) i +
          t ^ 2 • rootVector (P := P) (b := b) (-i) := by
  let := P.indexNeg
  rw [rootVector_of_pos i hi, rootVector_neg_of_pos i hi,
    rootUnipotent_neg_mulVec_transport_of_pos i hi,
    fUnipotent_mulVec_v_same,
    transportedVector_add, transportedVector_add,
    transportedVector_smul, transportedVector_smul]
  rfl

end

end

end RootPairing.IntegralGeckConstruction
