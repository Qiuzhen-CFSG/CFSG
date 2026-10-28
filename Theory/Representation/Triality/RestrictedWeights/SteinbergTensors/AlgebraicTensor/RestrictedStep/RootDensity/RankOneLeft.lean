module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootOperators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Restricted left highest strings on the actual D4 root groups

A positive root fixes a highest vector. The preserved Chevalley word
`h(t) = n(1)⁻¹ n(t)` acts on a vector of left exponent `n` by `t⁻ⁿ`.
Its rank-one Bruhat identity therefore gives reciprocal orbit polynomials
`p(s) = sⁿ q(s⁻¹)`. Comparing coefficients proves the degree bound and
identifies the top coefficient with the actual Weyl translate. For a binary
left highest weight the negative simple-root orbit is exactly `v + t E₋ᵢ v`.
No differential irreducibility, Frobenius, or concrete carrier is assumed.

Source: the ordinary-Frobenius argument underlying GLS3 Theorem 2.8.5 and
Corollary 2.8.6(a), and Steinberg, *Representations of Algebraic Groups*
(1963), §4.3. The scalar reflection proof follows the existing F4
`BasicDensity.NegativeCyclicity.RankOne`; the group calculation here uses
D4Geometry's actual raw words and the proved left-character adapter.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
omit [IsAlgClosed k] in
private theorem eval_reflect (q : Polynomial k) (N : ℕ) (hN : q.natDegree ≤ N)
    (t : k) (ht : t ≠ 0) :
    (q.reflect N).eval t = t ^ N * q.eval t⁻¹ := by
  let _ : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht)
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id k) (t⁻¹) N q hN
  have h' : (q.reflect N).eval t * (t⁻¹) ^ N = q.eval t⁻¹ := by
    simpa [invOf_eq_inv] using h
  calc
    (q.reflect N).eval t = ((q.reflect N).eval t * (t⁻¹) ^ N) * t ^ N := by
      rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero N ht), mul_one]
    _ = q.eval t⁻¹ * t ^ N := by rw [h']
    _ = t ^ N * q.eval t⁻¹ := mul_comm _ _

private theorem reciprocal_coeff (p q : Polynomial k) (n j : ℕ) (hk : j ≤ n)
    (h : ∀ t : k, t ≠ 0 → p.eval t = t ^ n * q.eval t⁻¹) :
    p.coeff j = q.coeff (n - j) := by
  let N := max n q.natDegree
  have hn : n ≤ N := le_max_left _ _
  have hq : q.natDegree ≤ N := le_max_right _ _
  have he : Polynomial.X ^ N * p = Polynomial.X ^ n * q.reflect N := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_of_finite_compl
      (by simp : ({t : k | t ≠ 0} : Set k)ᶜ.Finite)).mono
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, h t ht,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, eval_reflect q N hq t ht]
    ring
  have hc := congrArg (fun f : Polynomial k => f.coeff (j + N)) he
  rw [Polynomial.coeff_X_pow_mul, Polynomial.coeff_X_pow_mul', if_pos (by omega),
    Polynomial.coeff_reflect, Polynomial.revAt_le (by omega)] at hc
  have hi : N - (j + N - n) = n - j := by omega
  rwa [hi] at hc

/-- A polynomial reciprocal identity of weight `n` has no terms above `n`. -/
private theorem reciprocal_coeff_eq_zero (p q : Polynomial k) (n j : ℕ) (hk : n < j)
    (h : ∀ t : k, t ≠ 0 → p.eval t = t ^ n * q.eval t⁻¹) :
    p.coeff j = 0 := by
  let N := max n q.natDegree
  have hn : n ≤ N := le_max_left _ _
  have hq : q.natDegree ≤ N := le_max_right _ _
  have he : Polynomial.X ^ N * p = Polynomial.X ^ n * q.reflect N := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_of_finite_compl
      (by simp : ({t : k | t ≠ 0} : Set k)ᶜ.Finite)).mono
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, h t ht,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, eval_reflect q N hq t ht]
    ring
  have hc := congrArg (fun f : Polynomial k => f.coeff (j + N)) he
  rw [Polynomial.coeff_X_pow_mul, Polynomial.coeff_X_pow_mul', if_pos (by omega)] at hc
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (by simpa [max_eq_left hq] using
      (Polynomial.natDegree_reflect_le (p := q) (N := N)))
      (show N < j + N - n by omega))] at hc
  exact hc

variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- Every positive root fixes a genuine highest vector. -/
theorem positive_root_fixed_of_highWeight (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {χ : TorusWeight S.torus} {v : V} (hv : HasHighWeight ρ S.borel S.torus v χ)
    (α : S.roots.Root) (hα : α ∈ S.roots.positive) (t : k) :
    (ρ.action (S.chevalley.x α t)).val v = v := by
  let B := S.bigCell.data.positive_witness
  apply invariantLine_fixed_of_unipotent_subgroup ρ hρ S.borel B.unipotent
    v hv.1 B.radical.1 B.radical.2.1
  change S.chevalley.x α t ∈ B.unipotent.toSubgroup
  rw [B.root_generated]
  apply rootSubgroup_le_RootSubgroupGenerated S.roots hα
  change S.chevalley.x α t ∈ (S.roots.rootSubgroup α : Set (Variety.Point K))
  rw [← (S.chevalley_spec.1 α).2]
  exact ⟨t, rfl⟩

/-- The first coefficient of a positive root kills a genuine highest vector. -/
theorem positive_rootOperator_eq_zero_of_highWeight (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {χ : TorusWeight S.torus} {v : V} (hv : HasHighWeight ρ S.borel S.torus v χ)
    (α : S.roots.Root) (hα : α ∈ S.roots.positive) :
    rootOperator S ρ hρ α v = 0 := by
  apply (Module.finBasis k V).repr.injective
  ext i
  let l := (Module.finBasis k V).coord i
  have hp : curvePolynomial ρ hρ (rootMorphism S α) l v = Polynomial.C (l v) := by
    apply Polynomial.funext
    intro t
    rw [curvePolynomial_eval, rootMorphism_apply,
      positive_root_fixed_of_highWeight S ρ hρ hv α hα, Polynomial.eval_C]
  change l (curveOperator ρ hρ (rootMorphism S α) v) = l 0
  rw [dual_curveOperator, hp]
  simp

omit [IsAlgClosed k] in
private theorem simple_root_positive (S : D4Geometry K) (i : Fin 4) :
    S.rootEquiv.symm (typeDSimpleRootIndex 2 i) ∈ S.roots.positive := by
  let α := S.rootEquiv.symm (typeDSimpleRootIndex 2 i)
  have hsimple : α ∈ S.roots.simple := by
    apply (S.based.2.2.2.1 α).mpr
    simpa only [α, Equiv.apply_symm_apply, ← typeDRootPairing_baseEquiv_val] using
      (typeDRootPairing_baseEquiv 2 i).property
  exact ((S.realized.2.2.2.2.2.2.2.2.2.2.2.1 α).mp hsimple).1

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- A left highest weight has the negative exponent on the preserved raw word. -/
theorem raw_coroot_action_of_left_highWeight (S : D4Geometry K)
    (ρ : RationalRepresentation K V) {a : Weight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding a))
    (i : Fin 4) (t : kˣ) :
    (ρ.action (S.chevalley.h (S.rootEquiv.symm (typeDSimpleRootIndex 2 i)) t)).val v =
      (t : k) ^ (-a i) • v := by
  let z : Variety.Point (KMult k) := (dPointEquiv 1).symm (fun _ => t)
  have hz : dPointEquiv 1 z 0 = t := by simp [z]
  have hh := hv.2.2
    ((S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))).onPoints z)
  rw [S.coroot_spec, hz] at hh
  rw [S.leftWeightEmbedding_rawCoroot a i z] at hh
  simpa only [hz] using hh

private theorem highest_reciprocal_left [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) (n : ℕ) (v : V)
    (hx : ∀ t, (ρ.action (S.chevalley.x α t)).val v = v)
    (hh : ∀ t : kˣ, (ρ.action (S.chevalley.h α t)).val v =
      ((t : k)⁻¹) ^ n • v)
    (l : Module.Dual k V) (s : k) (hs : s ≠ 0) :
    (curvePolynomial ρ hρ (rootMorphism S (S.roots.neg α)) l v).eval s =
      s ^ n * (curvePolynomial ρ hρ (rootMorphism S α) l
        ((ρ.action (S.chevalley.n α 1)).val v)).eval s⁻¹ := by
  have hn (t : kˣ) : S.chevalley.n α t =
      S.chevalley.n α 1 * S.chevalley.h α t := by
    rw [S.chevalley_spec.2.2.1]
    group
  have hword (t : kˣ) : S.chevalley.x (S.roots.neg α) ((t : k)⁻¹) =
      S.chevalley.x α (t : k) * S.chevalley.n α 1 * S.chevalley.h α t *
        S.chevalley.x α (t : k) := by
    have hxx : S.chevalley.x α (t : k) * S.chevalley.x α (t : k) = 1 := by
      rw [S.chevalley_spec.2.2.2.1, CharTwo.add_self_eq_zero]
      rw [← rootMorphism_apply]
      have hz : kPlusPoint (0 : k) = 1 := by
        apply (additiveGroupPointEquiv k).injective
        rfl
      rw [hz, map_one]
    rw [mul_assoc (S.chevalley.x α _) (S.chevalley.n α 1), ← hn,
      S.chevalley_spec.2.1, CharTwo.neg_eq]
    simp only [← mul_assoc, hxx, one_mul]
    rw [mul_assoc, hxx, mul_one]
  have hw := hword (Units.mk0 s hs)⁻¹
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv] at hw
  rw [curvePolynomial_eval, curvePolynomial_eval, rootMorphism_apply,
    rootMorphism_apply, hw, map_mul, map_mul, map_mul]
  change l ((ρ.action _).val ((ρ.action _).val ((ρ.action _).val
    ((ρ.action _).val v)))) = _
  rw [hx, hh, map_smul, map_smul, map_smul]
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv, smul_eq_mul]

/-- A local highest string of left exponent `n` has no terms above `n`. -/
theorem negative_rootPolynomial_coeff_eq_zero_of_left_exponent [CharP k 2]
    (S : D4Geometry K) (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) (n : ℕ) (v : V)
    (hx : ∀ t, (ρ.action (S.chevalley.x α t)).val v = v)
    (hh : ∀ t : kˣ, (ρ.action (S.chevalley.h α t)).val v = ((t : k)⁻¹) ^ n • v)
    (l : Module.Dual k V) (j : ℕ) (hj : n < j) :
    (curvePolynomial ρ hρ (rootMorphism S (S.roots.neg α)) l v).coeff j = 0 :=
  reciprocal_coeff_eq_zero _ _ n j hj (highest_reciprocal_left S ρ hρ α n v hx hh l)

/-- The top coefficient of the local left highest string is its actual Weyl translate. -/
theorem negative_rootPolynomial_top_coeff_of_left_exponent [CharP k 2]
    (S : D4Geometry K) (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) (n : ℕ) (v : V)
    (hx : ∀ t, (ρ.action (S.chevalley.x α t)).val v = v)
    (hh : ∀ t : kˣ, (ρ.action (S.chevalley.h α t)).val v = ((t : k)⁻¹) ^ n • v)
    (l : Module.Dual k V) :
    (curvePolynomial ρ hρ (rootMorphism S (S.roots.neg α)) l v).coeff n =
      l ((ρ.action (S.chevalley.n α 1)).val v) := by
  have h := reciprocal_coeff _ _ n n le_rfl
    (highest_reciprocal_left S ρ hρ α n v hx hh l)
  simpa only [Nat.sub_self, curvePolynomial_coeff_zero] using h

/-- Restricted positive left coordinates bound every negative simple string by degree one. -/
theorem negative_simple_coeff_eq_zero_of_left_basic [CharP k 2]
    (S : D4Geometry K) (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {a : BasicWeight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding (coefficient a)))
    (i : Fin 4) (l : Module.Dual k V) (j : ℕ) (hj : 1 < j) :
    (curvePolynomial ρ hρ
      (rootMorphism S (S.roots.neg (S.rootEquiv.symm (typeDSimpleRootIndex 2 i)))) l v).coeff j = 0 := by
  let n : ℕ := if a i then 1 else 0
  apply negative_rootPolynomial_coeff_eq_zero_of_left_exponent S ρ hρ _ n v
  · exact positive_root_fixed_of_highWeight S ρ hρ hv _ (simple_root_positive S i)
  · intro t
    rw [raw_coroot_action_of_left_highWeight S ρ hv i t]
    cases ha : a i <;> simp [coefficient, n, ha]
  · dsimp [n]
    split <;> omega

/-- The actual negative simple root orbit of a restricted left highest vector
is its constant term plus its first root coefficient. -/
theorem negative_simple_action_of_left_basic [CharP k 2]
    (S : D4Geometry K) (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {a : BasicWeight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding (coefficient a)))
    (i : Fin 4) (t : k) :
    (ρ.action (S.chevalley.x
      (S.roots.neg (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))) t)).val v =
      v + t • rootOperator S ρ hρ
        (S.roots.neg (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))) v := by
  apply (Module.finBasis k V).repr.injective
  ext j
  let l := (Module.finBasis k V).coord j
  let α := S.roots.neg (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))
  let q := curvePolynomial ρ hρ (rootMorphism S α) l v
  have hq : q = Polynomial.C (l v) + Polynomial.C (q.coeff 1) * Polynomial.X := by
    ext m
    match m with
    | 0 => simp [q, curvePolynomial_coeff_zero]
    | 1 => simp
    | m + 2 =>
      rw [show q.coeff (m + 2) = 0 from
        negative_simple_coeff_eq_zero_of_left_basic S ρ hρ hv i l _ (by omega)]
      simp
  change l ((ρ.action (S.chevalley.x α t)).val v) =
    l (v + t • curveOperator ρ hρ (rootMorphism S α) v)
  rw [← rootMorphism_apply, ← curvePolynomial_eval]
  change q.eval t = _
  rw [hq]
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, map_add, map_smul, smul_eq_mul, dual_curveOperator]
  exact congrArg (l v + ·) (mul_comm _ _)

/-- At a positive binary coordinate the Weyl translate is the first lowering
coefficient, with the original pinning and left highest-weight character. -/
theorem simple_weyl_eq_rootOperator_of_left_coordinate_one [CharP k 2]
    (S : D4Geometry K) (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {a : BasicWeight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding (coefficient a)))
    (i : Fin 4) (hi : a i = true) :
    (ρ.action (S.chevalley.n (S.rootEquiv.symm (typeDSimpleRootIndex 2 i)) 1)).val v =
      rootOperator S ρ hρ (S.roots.neg (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))) v := by
  apply (Module.finBasis k V).repr.injective
  ext j
  let l := (Module.finBasis k V).coord j
  change l ((ρ.action (S.chevalley.n _ 1)).val v) =
    l (curveOperator ρ hρ (rootMorphism S _) v)
  rw [dual_curveOperator]
  symm
  apply negative_rootPolynomial_top_coeff_of_left_exponent S ρ hρ _ 1 v
  · exact positive_root_fixed_of_highWeight S ρ hρ hv _ (simple_root_positive S i)
  · intro t
    rw [raw_coroot_action_of_left_highWeight S ρ hv i t]
    simp [coefficient, hi]

/-- A coordinate equal to one gives a genuinely nonzero lowering operator on
the highest vector; the nonzero branches are not eliminated by convention. -/
theorem negative_simple_rootOperator_ne_zero_of_left_coordinate_one [CharP k 2]
    (S : D4Geometry K) (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {a : BasicWeight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding (coefficient a)))
    (i : Fin 4) (hi : a i = true) :
    rootOperator S ρ hρ (S.roots.neg (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))) v ≠ 0 := by
  intro hzero
  have h := (simple_weyl_eq_rootOperator_of_left_coordinate_one S ρ hρ hv i hi).trans hzero
  exact hv.1.1 ((ρ.action _).toLinearEquiv.injective (h.trans (map_zero _).symm))

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
