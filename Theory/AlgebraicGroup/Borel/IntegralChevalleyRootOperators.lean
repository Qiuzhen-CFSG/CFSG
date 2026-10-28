module

public import Theory.AlgebraicGroup.RootSystems.IntegralChevalleyRootLineBracket

/-!
# Integral Chevalley operators for every root

For a finite reduced crystallographic root pairing with a chosen base, this module packages
the integral all-root Chevalley construction on the finite free carrier
`(b.support ⊕ ι) → ℤ`.  Its root-indexed matrices and linear endomorphisms have integral
divided powers, are nilpotent, and act along the transported root strings.  On root vectors
their nonzero structure constants have absolute value `p + 1`; absent nonopposite root sums
give zero.  Each positive root and its negative also satisfy the four transported rank-one
actions on the two root vectors and their common Cartan vector.

The construction uses the canonical positive/negative root routes and integral Tits
conjugation from `IntegralAllRootOperators`.  Rank-two braid coherence makes the transported
root lines compatible, while `IntegralChevalleyBrackets` supplies the all-root constants.
For simple roots the integral matrices specialize, over any characteristic-zero field, to
Mathlib's Geck `e` and `f` matrices, both as matrices and on vectors.  Since every route stays
inside the component of its root, no irreducibility hypothesis is needed.  This is the
integral Chevalley-basis construction of Steinberg, *Lectures on Chevalley Groups*, Section 1,
Lemmas 1--3; compare GLS3, Theorem 1.12.1 and Remark 1.12.10.
-/

namespace RootPairing.IntegralGeckConstruction

@[expose] public section

noncomputable section

open Function
open scoped Matrix

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- The positive root operator sends its transported Cartan vector to twice its root vector. -/
lemma rootOperator_mulVec_rootCartanVector (i : ι) (hi : b.IsPos i) :
    rootOperator (P := P) (b := b) i *ᵥ
        rootCartanVector (P := P) (b := b) i =
      (2 : ℤ) • rootVector (P := P) (b := b) i := by
  rw [rootCartanVector, rootOperator_mulVec_transport_of_pos i hi,
    eMatrix_mulVec_u, transportedVector_smul, rootVector_of_pos i hi]
  norm_num

/-- The negative root operator sends the common Cartan vector to twice its root vector. -/
lemma rootOperator_neg_mulVec_rootCartanVector (i : ι) (hi : b.IsPos i) :
    letI := P.indexNeg
    rootOperator (P := P) (b := b) (-i) *ᵥ
        rootCartanVector (P := P) (b := b) i =
      (2 : ℤ) • rootVector (P := P) (b := b) (-i) := by
  let := P.indexNeg
  rw [rootCartanVector, rootOperator_neg_mulVec_transport_of_pos i hi,
    fMatrix_mulVec_u, transportedVector_smul, rootVector_neg_of_pos i hi]
  norm_num

/--
The finite free integral all-root Chevalley representation and its defining laws.

The fields retain both matrices and their bundled linear maps: later matrix-group constructions
use the former, while representation-theoretic consumers use the latter.  The root-string
fields state the full divided-power transport, so the specialized one-step and higher-string
formulas re-exported by this module apply directly.
-/
structure IntegralChevalleyRootOperators
    (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) [Fintype ι] [DecidableEq ι] where
  rootVector : ι → Carrier (b := b)
  rootCartanVector : ι → Carrier (b := b)
  rootOperator : ι → Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ
  rootDividedPower : ι → ℕ → Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ
  rootLinearOperator : ι → Module.End ℤ (Carrier (b := b))
  rootLinearOperator_apply : ∀ i x,
    rootLinearOperator i x = rootOperator i *ᵥ x
  carrierFinite : Module.Finite ℤ (Carrier (b := b))
  carrierFree : Module.Free ℤ (Carrier (b := b))
  dividedPower_zero : ∀ i, rootDividedPower i 0 = 1
  dividedPower_one : ∀ i, rootDividedPower i 1 = rootOperator i
  dividedPower_mul : ∀ i m n,
    rootDividedPower i m * rootDividedPower i n =
      (m + n).choose m • rootDividedPower i (m + n)
  operator_pow_eq_factorial_smul : ∀ i n,
    rootOperator i ^ n = n.factorial • rootDividedPower i n
  dividedPower_eq_zero_of_four_le : ∀ i n, 4 ≤ n → rootDividedPower i n = 0
  operator_isNilpotent : ∀ i, IsNilpotent (rootOperator i)
  dividedPower_rootString_pos : ∀ (i : ι) (_hi : b.IsPos i) (n : ℕ)
      (x : Carrier (b := b)),
    rootDividedPower i n *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word x =
      transportedVector (rootRoute (P := P) (b := b) i).word
        (eDividedPower (rootRoute (P := P) (b := b) i).simple n *ᵥ x)
  dividedPower_rootString_neg : ∀ (i : ι) (_hi : b.IsPos i) (n : ℕ)
      (x : Carrier (b := b)),
    letI := P.indexNeg
    rootDividedPower (-i) n *ᵥ
        transportedVector (rootRoute (P := P) (b := b) i).word x =
      transportedVector (rootRoute (P := P) (b := b) i).word
        (fDividedPower (rootRoute (P := P) (b := b) i).simple n *ᵥ x)
  bracket_signed : ∀ {i j k : ι}, P.root k = P.root i + P.root j →
    ∃ ε : ℤ, ε * ε = 1 ∧
      rootOperator i *ᵥ rootVector j =
        (ε * (P.chainBotCoeff i j + 1 : ℤ)) • rootVector k
  bracket_absolute : ∀ {i j k : ι}, P.root k = P.root i + P.root j →
    ∃ c : ℤ, c.natAbs = P.chainBotCoeff i j + 1 ∧
      rootOperator i *ᵥ rootVector j = c • rootVector k
  bracket_eq_zero : ∀ {i j : ι},
    (letI := P.indexNeg; j ≠ -i) →
    P.root i + P.root j ∉ Set.range P.root →
    rootOperator i *ᵥ rootVector j = 0
  opposite_root_sl2 : ∀ (i : ι) (_hi : b.IsPos i),
    letI := P.indexNeg
    rootOperator i *ᵥ rootVector (-i) = rootCartanVector i ∧
      rootOperator (-i) *ᵥ rootVector i = rootCartanVector i ∧
      rootOperator i *ᵥ rootCartanVector i = (2 : ℤ) • rootVector i ∧
      rootOperator (-i) *ᵥ rootCartanVector i = (2 : ℤ) • rootVector (-i)
  operator_simple : ∀ i : b.support, rootOperator i = eMatrix i
  operator_neg_simple : ∀ i : b.support,
    letI := P.indexNeg
    rootOperator (-i) = fMatrix i
  map_operator_simple : ∀ i : b.support,
    (rootOperator i).map (algebraMap ℤ R) = RootPairing.GeckConstruction.e i
  map_operator_neg_simple : ∀ i : b.support,
    letI := P.indexNeg
    (rootOperator (-i)).map (algebraMap ℤ R) = RootPairing.GeckConstruction.f i
  map_operator_simple_mulVec : ∀ (i : b.support) (x : Carrier (b := b)),
    (algebraMap ℤ R) ∘ (rootOperator i *ᵥ x) =
      RootPairing.GeckConstruction.e i *ᵥ ((algebraMap ℤ R) ∘ x)
  map_operator_neg_simple_mulVec : ∀ (i : b.support) (x : Carrier (b := b)),
    letI := P.indexNeg
    (algebraMap ℤ R) ∘ (rootOperator (-i) *ᵥ x) =
      RootPairing.GeckConstruction.f i *ᵥ ((algebraMap ℤ R) ∘ x)

/-- The canonical integral Chevalley operators obtained by integral Tits transport. -/
def integralChevalleyRootOperators : IntegralChevalleyRootOperators P b where
  rootVector := rootVector (P := P) (b := b)
  rootCartanVector := rootCartanVector (P := P) (b := b)
  rootOperator := rootOperator (P := P) (b := b)
  rootDividedPower := rootDividedPower (P := P) (b := b)
  rootLinearOperator := fun i => Matrix.toLin' (rootOperator (P := P) (b := b) i)
  rootLinearOperator_apply := by
    intro i x
    exact Matrix.toLin'_apply _ _
  carrierFinite := by infer_instance
  carrierFree := by infer_instance
  dividedPower_zero := rootDividedPower_zero (P := P) (b := b)
  dividedPower_one := rootDividedPower_one (P := P) (b := b)
  dividedPower_mul := rootDividedPower_mul (P := P) (b := b)
  operator_pow_eq_factorial_smul := rootOperator_pow_eq_factorial_smul (P := P) (b := b)
  dividedPower_eq_zero_of_four_le := by
    intro i n hn
    exact rootDividedPower_eq_zero_of_four_le (P := P) (b := b) i hn
  operator_isNilpotent := fun i => ⟨4, rootOperator_pow_four (P := P) (b := b) i⟩
  dividedPower_rootString_pos := rootDividedPower_mulVec_transport_of_pos (P := P) (b := b)
  dividedPower_rootString_neg :=
    rootDividedPower_neg_mulVec_transport_of_pos (P := P) (b := b)
  bracket_signed := rootOperator_mulVec_root_add_signed (P := P) (b := b)
  bracket_absolute := rootOperator_mulVec_root_add (P := P) (b := b)
  bracket_eq_zero := rootOperator_mulVec_root_eq_zero (P := P) (b := b)
  opposite_root_sl2 := by
    intro i hi
    let := P.indexNeg
    exact ⟨rootOperator_mulVec_opposite (P := P) (b := b) i hi,
      rootOperator_neg_mulVec (P := P) (b := b) i hi,
      rootOperator_mulVec_rootCartanVector (P := P) (b := b) i hi,
      rootOperator_neg_mulVec_rootCartanVector (P := P) (b := b) i hi⟩
  operator_simple := rootOperator_simple (P := P) (b := b)
  operator_neg_simple := rootOperator_neg_simple (P := P) (b := b)
  map_operator_simple := by
    intro i
    rw [rootOperator_simple, map_eMatrix]
  map_operator_neg_simple := by
    intro i
    let := P.indexNeg
    rw [rootOperator_neg_simple, map_fMatrix]
  map_operator_simple_mulVec := by
    intro i x
    rw [rootOperator_simple]
    exact map_eMatrix_mulVec (P := P) i x
  map_operator_neg_simple_mulVec := by
    intro i x
    let := P.indexNeg
    rw [rootOperator_neg_simple]
    exact map_fMatrix_mulVec (P := P) i x

/-- Integral Chevalley root operators exist for every finite reduced crystallographic pairing. -/
theorem integralChevalleyRootOperators_exists :
    Nonempty (IntegralChevalleyRootOperators P b) :=
  ⟨integralChevalleyRootOperators (P := P) (b := b)⟩

end

end

end RootPairing.IntegralGeckConstruction
