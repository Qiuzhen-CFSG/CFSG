module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.Inputs

/-!
# Constructing rational highest weights from fundamental modules

A highest vector survives in an irreducible composition factor of its cyclic
span. Tensoring two rational representations multiplies their torus characters,
hence adds their integral highest weights. Starting with the constant line and
four fundamental highest-weight modules, induction constructs every nonnegative
integral highest weight, and therefore every restricted one.

This argument needs neither tensor irreducibility nor Steinberg factorization.
The construction of the four fundamental modules remains an explicit premise.

Sources: GLS3, Theorem 1.14.6(d)--(e), and the rational existence input to
Theorem 2.8.2. The proved composition-factor and tensor lemmas are used directly;
the unresolved bundled `theorem_1_14_6` is not used.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- A highest vector survives in a rational irreducible composition factor. -/
theorem rationalFactor_exists_of_highWeight (S : Geometry K) {a : Weight}
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hr : IsRationalRepresentation ρ)
    (v : V) (hv : HasHighWeight ρ S.bigCell.data.B S.torus v (S.coordinateEmbedding a)) :
    ∃ A : RationalFactor K, HasHighestWeight S A a := by
  obtain ⟨C, Q, σ, hσ, w, hw⟩ := highWeight_compositionFactor_exists
    ρ hr S.bigCell.data.B S.torus v (S.coordinateEmbedding a) hv
  let : Nontrivial (C ⧸ Q) := ⟨⟨w, 0, hw.1.1⟩⟩
  exact ⟨{ Space := C ⧸ Q, action := σ, irreducible := hσ.1 }, w, hw⟩


/-- The constant one-dimensional action supplies the zero highest weight. -/
theorem rationalFactor_exists_zero (S : Geometry K) :
    ∃ A : RationalFactor K, HasHighestWeight S A 0 := by
  let ρ : RationalRepresentation K k := ⟨1⟩
  let e := Module.finBasis k k
  let coefficient : Fin (Module.finrank k k) → Fin (Module.finrank k k) →
      K.PolynomialFunction := fun i j =>
    algebraMap k K.PolynomialFunction (e.repr (e j) i)
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    e ρ.action coefficient coefficient
    (by intro i j g; rw [polynomialFunction_algebraMap_apply]; simp [ρ])
    (by intro i j g; rw [polynomialFunction_algebraMap_apply]; simp [ρ])
  have hr : IsRationalRepresentation ρ := by
    refine ⟨e, f, ?_⟩
    intro g
    exact glPointEquivOf_generalLinearRepresentationPoint e (ρ.action g)
  apply rationalFactor_exists_of_highWeight S ρ hr (1 : k)
  have hzero : S.coordinateEmbedding (0 : Weight) = 1 := S.weight.map_one
  refine ⟨⟨one_ne_zero, ?_⟩, one_ne_zero, ?_⟩
  · intro g hg
    exact ⟨1, by simp [ρ]⟩
  · intro t
    rw [hzero]
    simp only [ρ, MonoidHom.one_apply, Units.val_one, Module.End.one_apply, smul_eq_mul, mul_one]
    change (1 : k) = (dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 : k)
    exact (congrArg Units.val (congrFun (dPointEquiv_one (k := k) 1) 0)).symm

/-- Tensor two highest vectors and pass to an irreducible composition factor
to realize the sum of their weights. The tensor need not be irreducible. -/
theorem rationalFactor_exists_add (S : Geometry K) {a b : Weight}
    (ha : ∃ A : RationalFactor K, HasHighestWeight S A a)
    (hb : ∃ A : RationalFactor K, HasHighestWeight S A b) :
    ∃ A : RationalFactor K, HasHighestWeight S A (a + b) := by
  obtain ⟨A, v, hv⟩ := ha
  obtain ⟨C, w, hw⟩ := hb
  obtain ⟨ρ, ht, hr⟩ := rationalRepresentation_tensorProduct_exists
    A.action C.action A.irreducible.1 C.irreducible.1
  apply rationalFactor_exists_of_highWeight S ρ hr (TensorProduct.tmul k v w)
  have hcoord : S.coordinateEmbedding (a + b) =
      S.coordinateEmbedding a * S.coordinateEmbedding b :=
    S.weight.map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
  rw [hcoord]
  exact tensorProduct_hasHighWeight_tmul S.torus S.bigCell.data.B
    A.action C.action ρ ht v w (S.coordinateEmbedding a) (S.coordinateEmbedding b) hv hw

/-- Four fundamental highest-weight modules suffice for every nonnegative
integral weight, by repeated tensor products and composition factors. -/
theorem rationalFactor_exists_of_nonnegative_of_fundamentals (S : Geometry K)
    (hfund : FundamentalRationalExistence S) (a : Weight) (ha : ∀ i, 0 ≤ a i) :
    ∃ A : RationalFactor K, HasHighestWeight S A a := by
  classical
  let castWeight : (Fin 4 → ℕ) →+ Weight :=
    { toFun := fun f i => (f i : ℤ)
      map_zero' := by ext i; rfl
      map_add' := by intros; ext i; exact Nat.cast_add _ _ }
  have hzero : ∃ A : RationalFactor K, HasHighestWeight S A (castWeight 0) := by
    rw [map_zero]
    exact rationalFactor_exists_zero S
  have hadd (f g : Fin 4 → ℕ)
      (hf : ∃ A : RationalFactor K, HasHighestWeight S A (castWeight f))
      (hg : ∃ A : RationalFactor K, HasHighestWeight S A (castWeight g)) :
      ∃ A : RationalFactor K, HasHighestWeight S A (castWeight (f + g)) := by
    rw [map_add]
    exact rationalFactor_exists_add S hf hg
  have hsingle (i : Fin 4) (m : ℕ) :
      ∃ A : RationalFactor K, HasHighestWeight S A (castWeight (Pi.single i m)) := by
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
    (fun f => ∃ A : RationalFactor K, HasHighestWeight S A (castWeight f))
    (fun i => (a i).toNat) hzero hadd hsingle
  have heq : castWeight (fun i => (a i).toNat) = a := by
    ext i
    exact Int.toNat_of_nonneg (ha i)
  rwa [heq] at h

/-- In particular, the four fundamental constructions supply every restricted
weight for every exponent, including one. -/
theorem restrictedRationalExistence_of_fundamentals (S : Geometry K)
    (hfund : FundamentalRationalExistence S) (n : ℕ) : RestrictedRationalExistence S n := by
  intro a ha
  exact rationalFactor_exists_of_nonnegative_of_fundamentals S hfund a (fun i => (ha i).1)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
