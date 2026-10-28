module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.HighestWeightConstruction

/-!
# Realizing left highest weights through actual composition factors

Use the checked construction at the raw label `-a`, and addition of actual
characters. Four positive fundamental modules still have to be constructed.
Source: GLS3 1.14.6(d)--(e), and the rational existence input of 2.8.2.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

theorem leftRationalFactor_exists_of_highWeight (S : Geometry K) {a : Weight}
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hr : IsRationalRepresentation ρ)
    (v : V) (hv : HasHighWeight ρ S.bigCell.data.B S.torus v (S.leftWeightEmbedding a)) :
    ∃ A : RationalFactor K, HasLeftHighestWeight S A a :=
  rationalFactor_exists_of_highWeight S ρ hr v hv

theorem leftRationalFactor_exists_zero (S : Geometry K) :
    ∃ A : RationalFactor K, HasLeftHighestWeight S A 0 := by
  simpa only [hasLeftHighestWeight_iff, neg_zero] using rationalFactor_exists_zero S

theorem leftRationalFactor_exists_add (S : Geometry K) {a b : Weight}
    (ha : ∃ A : RationalFactor K, HasLeftHighestWeight S A a)
    (hb : ∃ A : RationalFactor K, HasLeftHighestWeight S A b) :
    ∃ A : RationalFactor K, HasLeftHighestWeight S A (a + b) := by
  simpa only [hasLeftHighestWeight_iff, neg_add] using rationalFactor_exists_add S ha hb

/-- Four fundamental highest-weight modules suffice for every nonnegative
integral weight, by repeated tensor products and composition factors. -/
theorem leftRationalFactor_exists_of_nonnegative_of_fundamentals (S : Geometry K)
    (hfund : LeftFundamentalRationalExistence S) (a : Weight) (ha : ∀ i, 0 ≤ a i) :
    ∃ A : RationalFactor K, HasLeftHighestWeight S A a := by
  classical
  let castWeight : (Fin 4 → ℕ) →+ Weight :=
    { toFun := fun f i => (f i : ℤ)
      map_zero' := by ext i; rfl
      map_add' := by intros; ext i; exact Nat.cast_add _ _ }
  have hzero : ∃ A : RationalFactor K, HasLeftHighestWeight S A (castWeight 0) := by
    rw [map_zero]
    exact leftRationalFactor_exists_zero S
  have hadd (f g : Fin 4 → ℕ)
      (hf : ∃ A : RationalFactor K, HasLeftHighestWeight S A (castWeight f))
      (hg : ∃ A : RationalFactor K, HasLeftHighestWeight S A (castWeight g)) :
      ∃ A : RationalFactor K, HasLeftHighestWeight S A (castWeight (f + g)) := by
    rw [map_add]
    exact leftRationalFactor_exists_add S hf hg
  have hsingle (i : Fin 4) (m : ℕ) :
      ∃ A : RationalFactor K, HasLeftHighestWeight S A (castWeight (Pi.single i m)) := by
    induction m with
    | zero => simpa using hzero
    | succ m ih =>
      rw [Pi.single_add]
      apply hadd _ _ ih
      have heq : castWeight (Pi.single i 1) = Pi.single i 1 := by
        ext j
        simp [castWeight, Pi.single_apply]
      rw [heq]
      exact hfund i
  have h := Pi.single_induction
    (fun f => ∃ A : RationalFactor K, HasLeftHighestWeight S A (castWeight f))
    (fun i => (a i).toNat) hzero hadd hsingle
  have heq : castWeight (fun i => (a i).toNat) = a := by
    ext i
    exact Int.toNat_of_nonneg (ha i)
  rwa [heq] at h

/-- In particular, the four fundamental constructions supply every restricted
weight for every exponent, including one. -/
theorem leftRestrictedRationalExistence_of_fundamentals (S : Geometry K)
    (hfund : LeftFundamentalRationalExistence S) (n : ℕ) : LeftRestrictedRationalExistence S n := by
  intro a ha
  exact leftRationalFactor_exists_of_nonnegative_of_fundamentals S hfund a (fun i => (ha i).1)


end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
