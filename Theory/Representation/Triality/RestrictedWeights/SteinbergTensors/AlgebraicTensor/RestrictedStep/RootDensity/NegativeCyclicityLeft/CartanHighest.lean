module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.HighestLine
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.Triangular
/-!
# Cartan eigenvalues on restricted D4 highest vectors

Coefficient comparison transfers actual root-curve intertwining to first
coefficients. The Weyl words are involutions in characteristic two and exchange
opposite root coefficients. At coordinate one the rank-one highest-string
formula identifies the Weyl translate with the lowering coefficient; at
coordinate zero the lowering coefficient vanishes. Thus each simple Cartan
bracket has precisely the binary highest-weight eigenvalue.

Source: Steinberg, *Representations of Algebraic Groups* (1963), §4;
GLS3 Theorem 2.8.5 and Corollary 2.8.6(a). The raw Chevalley words and the
left-character adapter are unchanged.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
@[expose] public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Actual root-curve intertwining passes to the first polynomial coefficients. -/
theorem rootOperator_intertwine (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (g : K.Point) (α β : S.roots.Root)
    (h : ∀ t, g * S.chevalley.x α t = S.chevalley.x β t * g) :
    (ρ.action g).val * rootOperator S ρ hρ α =
      rootOperator S ρ hρ β * (ρ.action g).val := by
  ext v
  apply (Module.finBasis k V).repr.injective
  ext i
  let l := (Module.finBasis k V).coord i
  change (l.comp (ρ.action g).val) (curveOperator ρ hρ (rootMorphism S α) v) =
    l (curveOperator ρ hρ (rootMorphism S β) ((ρ.action g).val v))
  rw [dual_curveOperator, dual_curveOperator]
  congr 1
  apply Polynomial.funext
  intro t
  rw [curvePolynomial_eval, curvePolynomial_eval, rootMorphism_apply, rootMorphism_apply]
  have he := congrArg (fun x => l ((ρ.action x).val v)) (h t)
  simpa only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.comp_apply] using he

omit [IsAlgClosed k] in
/-- Every actual Weyl word has square one in characteristic two. -/
theorem weyl_mul_self [CharP k 2] (S : D4Geometry K) (α : S.roots.Root) :
    S.chevalley.n α 1 * S.chevalley.n α 1 = 1 := by
  have hsq : S.chevalley.n α 1 * S.chevalley.n α 1 = S.chevalley.h α (-1) := by
    rcases S.chevalley_spec with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsq⟩
    exact hsq α
  have hunit : (-1 : kˣ) = 1 := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_one, CharTwo.neg_eq]
  rw [hsq, hunit, S.chevalley_spec.2.2.1, inv_mul_cancel]

/-- The actual Weyl words permute the actual first root coefficients. -/
theorem rootOperator_weyl [CharP k 2] (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (α β : S.roots.Root) :
    (ρ.action (S.chevalley.n β 1)).val * rootOperator S ρ hρ α =
      rootOperator S ρ hρ (S.roots.reflect β α) * (ρ.action (S.chevalley.n β 1)).val := by
  apply rootOperator_intertwine
  obtain ⟨sgn, hs, hx, _⟩ := S.chevalley_spec.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hn : (S.chevalley.n β 1)⁻¹ = S.chevalley.n β 1 :=
    inv_eq_of_mul_eq_one_right (weyl_mul_self S β)
  have hs1 : (sgn α β : k) = 1 := by
    rcases hs α β with h | h
    · rw [h, Units.val_one]
    · rw [h, Units.val_neg, Units.val_one, CharTwo.neg_eq]
  intro t
  have he := hx α β t
  rw [hn, hs1, one_mul] at he
  calc
    _ = (S.chevalley.n β 1 * S.chevalley.x α t * S.chevalley.n β 1) *
        S.chevalley.n β 1 := by rw [mul_assoc, weyl_mul_self, mul_one]
    _ = _ := by rw [he]

omit [IsAlgClosed k] in
private theorem reflect_neg_self (S : D4Geometry K) (α : S.roots.Root) :
    S.roots.reflect α (S.roots.neg α) = α := by
  apply S.rootEquiv.injective
  rw [S.based.2.1, S.based.2.2.1, RootPairing.reflectionPerm_self]

/-- A zero left simple coordinate kills the first lowering coefficient. -/
theorem negative_simple_eq_zero_of_left_coordinate_zero [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {a : BasicWeight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding (coefficient a)))
    (i : Fin 4) (hi : a i = false) :
    rootOperator S ρ hρ (S.roots.neg (simpleRoot S i)) v = 0 := by
  apply (Module.finBasis k V).repr.injective
  ext j
  let l := (Module.finBasis k V).coord j
  change l (curveOperator ρ hρ (rootMorphism S (S.roots.neg (simpleRoot S i))) v) = l 0
  rw [dual_curveOperator, map_zero]
  apply negative_rootPolynomial_coeff_eq_zero_of_left_exponent S ρ hρ _ 0 v
  · exact positive_root_fixed_of_highWeight S ρ hρ hv _ (simpleRoot_positive S i)
  · intro t
    rw [simpleRoot, raw_coroot_action_of_left_highWeight S ρ hv i t]
    simp only [coefficient, hi, Bool.false_eq_true, ↓reduceIte, neg_zero, zpow_zero,
      pow_zero]
  · decide

/-- A simple Cartan bracket acts by the corresponding binary left highest coordinate. -/
theorem cartanOperator_on_highest [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {a : BasicWeight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding (coefficient a)))
    (i : Fin 4) : cartanOperator S ρ hρ i v = (coefficient a i : k) • v := by
  have hz := positive_rootOperator_eq_zero_of_highWeight S ρ hρ hv _ (simpleRoot_positive S i)
  simp only [cartanOperator, LinearMap.sub_apply, Module.End.mul_apply, hz, map_zero, sub_zero]
  cases hi : a i with
  | false =>
    rw [negative_simple_eq_zero_of_left_coordinate_zero S ρ hρ hv i hi, map_zero]
    simp [coefficient, hi]
  | true =>
    have hnv : (ρ.action (S.chevalley.n (simpleRoot S i) 1)).val v =
        rootOperator S ρ hρ (S.roots.neg (simpleRoot S i)) v := by
      exact simple_weyl_eq_rootOperator_of_left_coordinate_one S ρ hρ hv i hi
    have he := congrArg (fun A : Module.End k V => A v)
      (rootOperator_weyl S ρ hρ (S.roots.neg (simpleRoot S i)) (simpleRoot S i))
    rw [reflect_neg_self] at he
    simp only [Module.End.mul_apply] at he
    simp only [coefficient, hi, ↓reduceIte, Int.cast_one, one_smul]
    calc
      _ = rootOperator S ρ hρ (simpleRoot S i)
          ((ρ.action (S.chevalley.n (simpleRoot S i) 1)).val v) := by rw [hnv]
      _ = (ρ.action (S.chevalley.n (simpleRoot S i) 1)).val
          (rootOperator S ρ hρ (S.roots.neg (simpleRoot S i)) v) := he.symm
      _ = (ρ.action (S.chevalley.n (simpleRoot S i) 1)).val
          ((ρ.action (S.chevalley.n (simpleRoot S i) 1)).val v) := by rw [hnv]
      _ = v := by
        rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, weyl_mul_self,
          map_one, Units.val_one, Module.End.one_apply]
end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
