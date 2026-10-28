module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.PolynomialSums
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Scalars
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-!
# Literal triality substitution on chart polynomials

The orbit order is (0,1,2), (4,5,6), (7,8,9), with singleton roots 3,10,11.
The substitution replaces each triple by t,t^q,t^(q^2), over the actual cubic
extension field, and each singleton by a parameter in the actual fixed field.
`coeff_restrictPolynomial` sums every monomial in the exponent fibre; it makes
no injectivity assumption and therefore retains collisions and cancellation.

These are polynomial identities, not constructions of global sections.
Source: the D4 ordering in `PositiveRootCoordinates.Roots`; Steinberg,
`Chapter2St2.tex`, 11.8 and 13.2(d)--13.3(a).
-/

@[expose] public noncomputable section
open scoped BigOperators Classical
open MvPolynomial Triality.Standard Triality.Standard.PositiveCoordinates
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.PolynomialBounds

abbrev MixedIndex := Fin 3 ⊕ Fin 3

def orbitVariable : Fin 12 → MixedIndex :=
  ![.inl 0, .inl 0, .inl 0, .inr 0, .inl 1, .inl 1, .inl 1,
    .inl 2, .inl 2, .inl 2, .inr 1, .inr 2]

def orbitPower : Fin 12 → ℕ := ![0, 1, 2, 0, 0, 1, 2, 0, 1, 2, 0, 0]

def foldExponent (q : ℕ) (d : Fin 12 →₀ ℕ) : MixedIndex →₀ ℕ :=
  ∑ i, Finsupp.single (orbitVariable i) (q ^ orbitPower i * d i)

lemma foldExponent_cubic (q : ℕ) (d : Fin 12 →₀ ℕ) (j : Fin 3) :
    foldExponent q d (.inl j) =
      ![d 0 + q * d 1 + q^2 * d 2, d 4 + q * d 5 + q^2 * d 6,
        d 7 + q * d 8 + q^2 * d 9] j := by
  fin_cases j <;> simp [foldExponent, orbitVariable, orbitPower, Fin.sum_univ_succ, add_assoc]

lemma foldExponent_singleton (q : ℕ) (d : Fin 12 →₀ ℕ) (j : Fin 3) :
    foldExponent q d (.inr j) = ![d 3, d 10, d 11] j := by
  fin_cases j <;> simp [foldExponent, orbitVariable, orbitPower, Fin.sum_univ_succ]

variable {k : Type*} [Field k]

def restrictPolynomial (q : ℕ) (p : MvPolynomial (Fin 12) k) :
    MvPolynomial MixedIndex k :=
  ∑ d ∈ p.support, monomial (foldExponent q d) (p.coeff d)

lemma monomial_foldExponent (q : ℕ) (d : Fin 12 →₀ ℕ) (c : k) :
    monomial (foldExponent q d) c =
      eval₂Hom C (fun i => (X (orbitVariable i)) ^ (q ^ orbitPower i)) (monomial d c) := by
  rw [foldExponent, monomial_sum_index, eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [← X_pow_eq_monomial, ← pow_mul]

lemma restrictPolynomial_eq_eval₂ (q : ℕ) (p : MvPolynomial (Fin 12) k) :
    restrictPolynomial q p =
      eval₂Hom C (fun i => X (orbitVariable i) ^ (q ^ orbitPower i)) p := by
  rw [restrictPolynomial]
  simp_rw [monomial_foldExponent]
  rw [← map_sum, p.support_sum_monomial_coeff]

lemma coeff_restrictPolynomial (q : ℕ) (p : MvPolynomial (Fin 12) k)
    (e : MixedIndex →₀ ℕ) :
    (restrictPolynomial q p).coeff e =
      ∑ d ∈ p.support with foldExponent q d = e, p.coeff d := by
  simp [restrictPolynomial, coeff_sum, coeff_monomial, Finset.sum_filter]

lemma support_restrictPolynomial (q : ℕ) (p : MvPolynomial (Fin 12) k) :
    (restrictPolynomial q p).support ⊆ p.support.image (foldExponent q) := by
  intro e he
  obtain ⟨d, hd, hde⟩ := Finset.mem_biUnion.mp
    (MvPolynomial.support_sum he)
  have hc : p.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  simp only [support_monomial, if_neg hc, Finset.mem_singleton] at hde
  exact Finset.mem_image.mpr ⟨d, hd, hde.symm⟩


/-- The six actual coordinate fields, with three cubic and three fixed factors. -/
abbrev CoordinateField (P : Parameters) : MixedIndex → Type :=
  Sum.elim (fun _ => ExtensionField P) (fun _ => fixedField P)

instance coordinateField (P : Parameters) (i : MixedIndex) : Field (CoordinateField P i) := by
  cases i <;> unfold CoordinateField <;> dsimp <;> infer_instance

instance coordinateFintype (P : Parameters) (i : MixedIndex) : Fintype (CoordinateField P i) := by
  cases i <;> unfold CoordinateField <;> dsimp <;> exact Fintype.ofFinite _

@[simp] lemma card_cubic (P : Parameters) (j : Fin 3) :
    Fintype.card (CoordinateField P (.inl j)) = P.q^3 := by
  rw [← Nat.card_eq_fintype_card]
  exact card_extensionField P

@[simp] lemma card_singleton (P : Parameters) (j : Fin 3) :
    Fintype.card (CoordinateField P (.inr j)) = P.q := by
  rw [← Nat.card_eq_fintype_card]
  exact card_fixedField P

def parameterEquiv (P : Parameters) : (∀ i, CoordinateField P i) ≃ OrbitParameters P where
  toFun x := (fun j => x (.inl j), fun j => x (.inr j))
  invFun x := fun i => match i with | .inl j => x.1 j | .inr j => x.2 j
  left_inv x := by funext i; cases i <;> rfl
  right_inv x := rfl

def coordinateEmbedding (P : Parameters) (ι : ExtensionField P →+* k) :
    ∀ i, CoordinateField P i →+* k :=
  fun i => match i with
    | .inl _ => ι
    | .inr _ => ι.comp (fixedField P).subtype

set_option backward.isDefEq.respectTransparency false in
lemma eval_restrictPolynomial (P : Parameters) (ι : ExtensionField P →+* k)
    (p : MvPolynomial (Fin 12) k) (x : ∀ i, CoordinateField P i) :
    eval (fun i => coordinateEmbedding P ι i (x i)) (restrictPolynomial P.q p) =
      eval (fun i => ι (expand P (parameterEquiv P x) i)) p := by
  rw [restrictPolynomial_eq_eval₂]
  change eval _ (eval₂ _ _ p) = _
  rw [← eval_assoc]
  apply congrArg (fun v : Fin 12 → k => eval v p)
  funext i
  fin_cases i <;>
    simp [coordinateEmbedding, parameterEquiv, expand, orbitVariable, orbitPower,
      fieldFrobenius_apply, map_pow, pow_mul, pow_two]

/-- Exponent q-1 in each of the twelve actual ordered root coordinates. -/
def rootTopExponent (q : ℕ) : Fin 12 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => q-1)

@[simp] lemma rootTopExponent_apply (q : ℕ) (i : Fin 12) :
    rootTopExponent q i = q-1 := rfl

/-- The root-top exponent maps to the mixed-field top, also when q = 2. -/
lemma foldExponent_rootTop (P : Parameters) :
    foldExponent P.q (Finsupp.equivFunOnFinite.symm (fun _ => P.q - 1)) =
      PolynomialSums.topExponent (CoordinateField P) := by
  have hq : 1 ≤ P.q := by have := P.q_ge_two; omega
  have hq' : P.q - 1 + 1 = P.q := Nat.sub_add_cancel hq
  have hq3 : P.q^3 - 1 + 1 = P.q^3 := Nat.sub_add_cancel (one_le_pow₀ hq)
  ext i
  cases i with
  | inl j =>
    rw [foldExponent_cubic, PolynomialSums.topExponent_apply, card_cubic]
    fin_cases j <;> dsimp <;> nlinarith
  | inr j =>
    rw [foldExponent_singleton, PolynomialSums.topExponent_apply, card_singleton]
    fin_cases j <;> rfl

/-- A condition on ALL original terms transports to the required mixed support. -/
lemma support_condition_of_fold (P : Parameters) (p : MvPolynomial (Fin 12) k)
    (hp : ∀ d ∈ p.support,
      foldExponent P.q d ≠ PolynomialSums.topExponent (CoordinateField P) →
        ∃ i, foldExponent P.q d i < Fintype.card (CoordinateField P i) - 1) :
    ∀ e ∈ (restrictPolynomial P.q p).support,
      e ≠ PolynomialSums.topExponent (CoordinateField P) →
        ∃ i, e i < Fintype.card (CoordinateField P i) - 1 := by
  intro e he hne
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_restrictPolynomial P.q p he)
  exact hp d hd hne

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.PolynomialBounds
