module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.WeightedGauss
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.MixedCoefficients
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.TorusDistributions
/-!
# Opposite divided powers and torus-binomial membership

Apply a covector to Gauss decomposition and extract both scalar polynomial
coefficients. Finite spectral decomposition then turns the identities on all
integral eigenvectors into endomorphism identities. Equal-index straightening
recursively expresses each torus binomial in the algebra of opposite root
coefficients; Vandermonde handles arbitrary shifts.

There is no nonzero-vector assumption, polynomial-degree bound, irreducibility
hypothesis, or normalization input. Binomials are formed in ℤ before casting.
The existing `rankOneChart_rescale` transports all coefficients to the actual
root parameters, and `rankOneAlgebra_eq_chart` transports algebra membership.

Source: SL₂ integral divided powers underlying Steinberg,
*Representations of algebraic groups* (1963), §§2–3.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
open AlgebraicTensor.RestrictedStep
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private theorem straightening_of_expansion (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y : Morphism (KPlus k) K)
    (m : ℤ) (v : V) (M N : ℕ)
    (hM : ∀ b, M ≤ b → curveCoefficient rho hr x b = 0)
    (hN : ∀ a, N ≤ a → curveCoefficient rho hr y a = 0)
    (hgauss : ∀ s t : k, 1+s*t ≠ 0 →
      (rho.action (x.onPoints (kPlusPoint s))).val
        ((rho.action (y.onPoints (kPlusPoint t))).val v) =
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range M,
        (t^a * s^b * (1+s*t)^(m+(b:ℤ)-(a:ℤ))) •
          curveCoefficient rho hr y a (curveCoefficient rho hr x b v))
    (i j : ℕ) :
    curveCoefficient rho hr x i (curveCoefficient rho hr y j v) =
      ∑ r ∈ Finset.range (min i j + 1),
        ((Ring.choose (m+(i:ℤ)-(j:ℤ)) r : ℤ) : k) •
          curveCoefficient rho hr y (j-r) (curveCoefficient rho hr x (i-r) v) := by
  classical
  apply (Module.finBasis k V).repr.injective
  ext z
  let l := (Module.finBasis k V).coord z
  change l (curveCoefficient rho hr x i (curveCoefficient rho hr y j v)) = l _
  rw [dual_curveCoefficient]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply rankOne_mixed_laurent_coeff M N i j
    (fun a b => l (curveCoefficient rho hr y a (curveCoefficient rho hr x b v))) m
    (fun s => curvePolynomial rho hr y (l.comp (rho.action (x.onPoints (kPlusPoint s))).val) v)
    (curvePolynomial rho hr x l (curveCoefficient rho hr y j v))
  · intro a b hb
    simp [hM b hb]
  · intro a b ha
    simp [hN a ha]
  · intro s
    rw [curvePolynomial_eval, ← dual_curveCoefficient]
    rfl
  · intro s t ht
    rw [curvePolynomial_eval, LinearMap.comp_apply, hgauss s t ht]
    simp only [map_sum, map_smul, smul_eq_mul]

/-- Opposite divided powers on every integral eigenvector, including zero.
The binomial is evaluated in the integers before casting to the field. -/
theorem rankOne_straightening (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m : ℤ) (v : V) (hv : rankOneHasWeight f rho m v) (i j : ℕ) :
    curveCoefficient rho hr (f.comp standardSL2UpperMorphism) i
      (curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j v) =
      ∑ r ∈ Finset.range (min i j + 1),
        ((Ring.choose (m+(i:ℤ)-(j:ℤ)) r : ℤ) : k) •
          curveCoefficient rho hr (f.comp standardSL2LowerMorphism) (j-r)
            (curveCoefficient rho hr (f.comp standardSL2UpperMorphism) (i-r) v) := by
  obtain ⟨M, N, hM, hN, hg⟩ := rankOne_weighted_gauss f rho hr m v hv
  exact straightening_of_expansion rho hr _ _ m v M N hM hN hg i j

/-- Reversing the roots negates the integral direct-diagonal weight. -/
theorem rankOne_straightening_reverse (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (m : ℤ) (v : V) (hv : rankOneHasWeight f rho m v) (i j : ℕ) :
    curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j
      (curveCoefficient rho hr (f.comp standardSL2UpperMorphism) i v) =
      ∑ r ∈ Finset.range (min i j + 1),
        ((Ring.choose (-m+(j:ℤ)-(i:ℤ)) r : ℤ) : k) •
          curveCoefficient rho hr (f.comp standardSL2UpperMorphism) (i-r)
            (curveCoefficient rho hr (f.comp standardSL2LowerMorphism) (j-r) v) := by
  obtain ⟨M, N, hM, hN, hg⟩ := rankOne_weighted_gauss_reverse f rho hr m v hv
  have h := straightening_of_expansion rho hr
    (f.comp standardSL2LowerMorphism) (f.comp standardSL2UpperMorphism)
    (-m) v N M hN hM (fun s t ht => ?_) j i
  · simpa only [min_comm] using h
  simpa only [mul_comm s t, Morphism.comp, Morphism.onPoints, Variety.Morphism.comp,
    MonoidHom.coe_mk, OneHom.coe_mk] using hg t s (by simpa only [mul_comm s t] using ht)

/-- Straightening as an endomorphism identity, using actual torus projectors. -/
theorem rankOne_straightening_operator (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (i j : ℕ) :
    curveCoefficient rho hr (f.comp standardSL2UpperMorphism) i *
      curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j =
      ∑ r ∈ Finset.range (min i j + 1),
        curveCoefficient rho hr (f.comp standardSL2LowerMorphism) (j-r) *
          curveCoefficient rho hr (f.comp standardSL2UpperMorphism) (i-r) *
            rankOneTorusBinomial f rho hr ((i:ℤ)-(j:ℤ)) r := by
  apply rankOne_weight_ext f rho hr
  intro m v hv
  simp only [LinearMap.sum_apply, Module.End.mul_apply]
  simp_rw [rankOneTorusBinomial_apply_weight f rho hr _ m _ v hv, map_smul]
  simpa only [sub_eq_add_neg, add_assoc] using rankOne_straightening f rho hr m v hv i j

/-- Equal-index straightening puts each unshifted torus binomial operator
inside the algebra generated by the truncated opposite roots. -/
theorem rankOneTorusBinomial_mem (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (q j : ℕ) (hj : j < q) :
    rankOneTorusBinomial f rho hr 0 j ∈ rankOneCurveAlgebra rho hr
      (f.comp standardSL2UpperMorphism) (f.comp standardSL2LowerMorphism) q := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    let A := rankOneCurveAlgebra rho hr
      (f.comp standardSL2UpperMorphism) (f.comp standardSL2LowerMorphism) q
    have he := rankOne_straightening_operator f rho hr j j
    simp only [min_self, sub_self, Finset.sum_range_succ, Nat.sub_self,
      curveCoefficient_zero, one_mul] at he
    have heq : rankOneTorusBinomial f rho hr 0 j =
        curveCoefficient rho hr (f.comp standardSL2UpperMorphism) j *
          curveCoefficient rho hr (f.comp standardSL2LowerMorphism) j -
        ∑ r ∈ Finset.range j,
          curveCoefficient rho hr (f.comp standardSL2LowerMorphism) (j-r) *
            curveCoefficient rho hr (f.comp standardSL2UpperMorphism) (j-r) *
              rankOneTorusBinomial f rho hr 0 r := (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using he.symm))
    rw [heq]
    apply A.sub_mem
    · exact A.mul_mem (rankOneCurveAlgebra_first rho hr _ _ q j hj)
        (rankOneCurveAlgebra_second rho hr _ _ q j hj)
    · apply A.sum_mem
      intro r hr'
      have hrj := Finset.mem_range.mp hr'
      exact A.mul_mem (A.mul_mem
        (rankOneCurveAlgebra_second rho hr _ _ q (j-r) (by omega))
        (rankOneCurveAlgebra_first rho hr _ _ q (j-r) (by omega)))
        (ih r hrj (by omega))

/-- Vandermonde gives the same membership for every integral shift. -/
theorem rankOneTorusBinomial_shift_mem (f : Morphism (slVariety k 2) K)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (q j : ℕ) (hj : j < q) (d : ℤ) :
    rankOneTorusBinomial f rho hr d j ∈ rankOneCurveAlgebra rho hr
      (f.comp standardSL2UpperMorphism) (f.comp standardSL2LowerMorphism) q := by
  rw [rankOneTorusBinomial_vandermonde]
  apply Subalgebra.sum_mem
  intro r hr'
  exact Subalgebra.smul_mem _ (rankOneTorusBinomial_mem f rho hr q r
    (by have := Finset.mem_range.mp hr'; omega)) _

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
