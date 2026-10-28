module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.Operations
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.Geometry

/-!
# Highest weights of the actual rational D4 tensors

Pullback along Frobenius multiplies a torus character by two. Pure tensors
of nonzero highest-weight vectors remain nonzero and multiply their characters.
Induction therefore gives the exact highest weight of the tensor from
`Construction`, and the genuine character-lattice isomorphism identifies it
with the sum of the binary coordinate vectors weighted by powers of two.
No tensor irreducibility is used in this argument.

Source: the proof of GLS3, Corollary 2.8.6(a), using Definition 2.8.3,
Remark 2.8.4 and the elementary tensor-weight calculation of 1.14.9(a);
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
private theorem character_pow (T : ClosedSubgroup K) (χ : TorusWeight T)
    (n : ℕ) (t : Variety.Point T.carrierVariety) :
    (χ ^ n).pointCharacter t = χ.pointCharacter t ^ n := by
  induction n with
  | zero =>
    change (dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 : k) = _
    rw [dPointEquiv_one]
    simp
  | succ n ih =>
    rw [pow_succ]
    change (dPointEquiv 1 ((χ ^ n).onPoints t * χ.onPoints t) 0 : k) = _
    rw [dPointEquiv_mul]
    change (χ ^ n).pointCharacter t * χ.pointCharacter t = _
    rw [ih, pow_succ]

omit [IsAlgClosed k] in
/-- Pullback along a map acting by the `r`th power on the torus multiplies
highest weights by `r`. This concerns the actual torus characters. -/
theorem pullback_hasHighWeight_pow (B T : ClosedSubgroup K)
    (φ : Theory.AlgebraicGroup.Morphism K K) (r : ℕ)
    (hB : ∀ b, b ∈ B → φ.onPoints b ∈ B)
    (hT : ∀ t : Variety.Point T.carrierVariety,
      φ.onPoints (T.includePoint t) = T.includePoint (t ^ r))
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (v : V) (χ : TorusWeight T)
    (hv : HasHighWeight ρ B T v χ) :
    HasHighWeight (pullback φ ρ) B T v (χ ^ r) := by
  refine ⟨⟨hv.1.1, fun b hb => hv.1.2 _ (hB b hb)⟩, hv.2.1, ?_⟩
  intro t
  change (ρ.action (φ.onPoints (T.includePoint t))).1 v = _
  rw [hT, hv.2.2 (t ^ r), map_pow, character_pow]

omit [IsAlgClosed k] in
/-- Frobenius iterates act on the torus by the corresponding power of two. -/
theorem OrdinaryFrobenius.iterate_torus {S : D4Geometry K}
    (F : OrdinaryFrobenius S) (n : ℕ) (t : Variety.Point S.torus.carrierVariety) :
    (iterate F.morphism n).onPoints (S.torus.includePoint t) =
      S.torus.includePoint (t ^ (2 ^ n)) := by
  induction n with
  | zero =>
    change S.torus.includePoint t = S.torus.includePoint (t ^ 1)
    rw [pow_one]
  | succ n ih =>
    change F.morphism.onPoints ((iterate F.morphism n).onPoints (S.torus.includePoint t)) = _
    rw [ih, F.torus_formula, ← pow_mul, ← pow_succ]

omit [IsAlgClosed k] in
/-- The chosen positive Borel is stable under all Frobenius iterates. -/
theorem OrdinaryFrobenius.iterate_borel {S : D4Geometry K}
    (F : OrdinaryFrobenius S) (n : ℕ) (b : Variety.Point K) (hb : b ∈ S.borel) :
    (iterate F.morphism n).onPoints b ∈ S.borel := by
  induction n with
  | zero => exact hb
  | succ n ih => exact F.borel_stable _ ih

/-- The tensor's character is the product of the Frobenius-twisted basic characters. -/
def tensorCharacter (T : ClosedSubgroup K) (e : Weight ↪ TorusWeight T)
    (a : ℕ → BasicWeight) (n : ℕ) : TorusWeight T :=
  ∏ i ∈ Finset.range n, e (coefficient (a i)) ^ (2 ^ i)

/-- The sum of the simple-coroot coordinate vectors, with ordinary Frobenius exponents. -/
def tensorWeight (a : ℕ → BasicWeight) (n : ℕ) : Weight :=
  ∑ i ∈ Finset.range n, (2 ^ i : ℕ) • coefficient (a i)

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
/-- The product of characters is precisely addition in the genuine character lattice. -/
theorem tensorCharacter_eq_weight (S : D4Geometry K) (a : ℕ → BasicWeight) (n : ℕ) :
    tensorCharacter S.torus S.weightEmbedding a n = S.weightEmbedding (tensorWeight a n) := by
  unfold tensorCharacter tensorWeight
  change (∏ i ∈ Finset.range n, S.characters (Multiplicative.ofAdd (coefficient (a i))) ^ (2 ^ i)) =
    S.characters (Multiplicative.ofAdd (∑ i ∈ Finset.range n, (2 ^ i : ℕ) • coefficient (a i)))
  rw [ofAdd_sum, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [ofAdd_nsmul, map_pow]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor of actual highest-weight vectors has the expected highest weight.
This statement does not assume tensor irreducibility. -/
theorem rationalTensor_hasHighWeight (S : D4Geometry K)
    (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.weightEmbedding)
    (a : ℕ → BasicWeight) (n : ℕ) :
    ∃ v, HasHighWeight (rationalTensor A.factor (pointEnd F.morphism) a n)
      S.borel S.torus v (tensorCharacter S.torus S.weightEmbedding a n) := by
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
      (A.factor (a n)).action w (S.weightEmbedding (coefficient (a n))) hw
    have htw : HasHighWeight
        (algebraicAction (twistedFactor A.factor (pointEnd F.morphism) (MonoidHom.id _) (a n) n).ρ)
        S.borel S.torus w (S.weightEmbedding (coefficient (a n)) ^ (2 ^ n)) := by
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
theorem rationalTensor_hasHighWeight_sum (S : D4Geometry K)
    (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.weightEmbedding)
    (a : ℕ → BasicWeight) (n : ℕ) :
    ∃ v, HasHighWeight (rationalTensor A.factor (pointEnd F.morphism) a n)
      S.borel S.torus v (S.weightEmbedding (tensorWeight a n)) := by
  simpa only [tensorCharacter_eq_weight] using rationalTensor_hasHighWeight S F A a n

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
