module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.HighestWeights

/-!
# Actual tensors in left highest-weight coordinates

The generic pullback and pure-tensor proofs give the same binary sum of
positive coordinates. The family remains `RationalBasicFamily` at the new
embedding; its existence and tensor irreducibility are not assumed here.
Source: GLS3 1.14.9(a), 2.8.3--6 and Steinberg §13.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
/-- Products of actual left characters add the positive integral coordinates. -/
theorem leftTensorCharacter_eq_weight (S : D4Geometry K) (a : ℕ → BasicWeight) (n : ℕ) :
    tensorCharacter S.torus S.leftWeightEmbedding a n =
      S.leftWeightEmbedding (tensorWeight a n) := by
  unfold tensorCharacter tensorWeight
  rw [S.leftWeightEmbedding_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact (S.leftWeightEmbedding_nsmul (2 ^ i) (coefficient (a i))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The tensor of actual highest-weight vectors has the expected highest weight.
This statement does not assume tensor irreducibility. -/
theorem leftRationalTensor_hasHighWeight (S : D4Geometry K)
    (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (a : ℕ → BasicWeight) (n : ℕ) :
    ∃ v, HasHighWeight (rationalTensor A.factor (pointEnd F.morphism) a n)
      S.borel S.torus v (tensorCharacter S.torus S.leftWeightEmbedding a n) := by
  induction n with
  | zero =>
    refine ⟨(1 : k), ⟨(one_ne_zero : (1 : k) ≠ 0), fun b _ => ⟨1, ?_⟩⟩, (one_ne_zero : (1 : k) ≠ 0), ?_⟩
    · change (Representation.trivial k (Variety.Point K) k b) 1 = (1 : k) • 1
      simp [Representation.trivial]
    · intro t
      change (Representation.trivial k (Variety.Point K) k (S.torus.includePoint t)) 1 = _
      simp only [tensorCharacter, Finset.range_zero, Finset.prod_empty]
      change (1 : k) = (dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 : k) • 1
      rw [dPointEquiv_one]
      simp
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih
    obtain ⟨w, hw⟩ := A.highest (a n)
    have ht := pullback_hasHighWeight_pow S.borel S.torus (iterate F.morphism n)
      (2 ^ n) (F.iterate_borel n) (F.iterate_torus n)
      (A.factor (a n)).action w (S.leftWeightEmbedding (coefficient (a n))) hw
    have htw : HasHighWeight
        (algebraicAction (twistedFactor A.factor (pointEnd F.morphism) (MonoidHom.id _) (a n) n).ρ)
        S.borel S.torus w (S.leftWeightEmbedding (coefficient (a n)) ^ (2 ^ n)) := by
      rw [twistedFactor_eq_pullback]
      exact ht
    refine ⟨TensorProduct.tmul k v w, ?_⟩
    have hh := tensorProduct_hasHighWeight_tmul S.torus S.borel
      (rationalTensor A.factor (pointEnd F.morphism) a n)
      (algebraicAction (twistedFactor A.factor (pointEnd F.morphism) (MonoidHom.id _) (a n) n).ρ)
      (rationalTensor A.factor (pointEnd F.morphism) a (n + 1))
      (fun g x y => by
        rfl)
      v w _ _ hv htw
    simpa only [tensorCharacter, Finset.prod_range_succ] using hh

/-- The actual highest weight is `∑ i < n, 2^i coefficient(a_i)` in simple-coroot coordinates. -/
theorem leftRationalTensor_hasHighWeight_sum (S : D4Geometry K)
    (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (a : ℕ → BasicWeight) (n : ℕ) :
    ∃ v, HasHighWeight (rationalTensor A.factor (pointEnd F.morphism) a n)
      S.borel S.torus v (S.leftWeightEmbedding (tensorWeight a n)) := by
  simpa only [leftTensorCharacter_eq_weight] using leftRationalTensor_hasHighWeight S F A a n

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
