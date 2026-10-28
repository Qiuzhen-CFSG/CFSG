module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootOperators
public import Mathlib.Algebra.Polynomial.Reverse
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

/-!
# Detecting the Borel/coroot sign mismatch

The current `D4Geometry` couples the positive-root Borel to the Chevalley
convention `h(t) = n(1)⁻¹ n(t)`. For the left action used by
`RationalRepresentation`, these choices do not admit a nonzero binary
highest weight with the stated positive character--coroot coordinates.
`basic_highWeight_eq_zero` proves this obstruction from the actual regular
root curves, without assuming irreducibility or any representation theorem.

The rank-one calculation is short. In characteristic two, write `x` and `y`
for opposite root groups and `n = n(1)`. If `x(t)v = v` and `h(t)v = t v`,
then `y(t⁻¹)v = t x(t)n v` for nonzero `t`. Applying a covector gives
polynomials `q(t⁻¹) = t p(t)`. Polynomial reflection forces `q(0) = 0`.
A covector with value one on `v` gives a contradiction.

The intended restricted range is GLS3 Definition 2.8.1(a), used in
Theorem 2.8.5 and Corollary 2.8.6(a). Compare also the rank-one conventions
in `refs/KGroup/GLS3/Chapter1.tex`, §§1.12 and 1.14. The obstruction must be
resolved at the Borel/character interface before claiming the nonzero
restricted branches. It is deliberately not used to prove a density theorem
by vacuity. The geometric carrier itself is not asserted to be inconsistent.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
namespace RootDensityConventions
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma eval_reflect_natDegree (q : Polynomial k) (t : k) (ht : t ≠ 0) :
    (q.reflect q.natDegree).eval t = t ^ q.natDegree * q.eval t⁻¹ := by
  let _ : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht)
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id k) (t⁻¹)
    q.natDegree q le_rfl
  have h' : (q.reflect q.natDegree).eval t * (t⁻¹) ^ q.natDegree =
      q.eval t⁻¹ := by
    simpa [invOf_eq_inv] using h
  calc
    (q.reflect q.natDegree).eval t =
        ((q.reflect q.natDegree).eval t * (t⁻¹) ^ q.natDegree) *
          t ^ q.natDegree := by
      rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero q.natDegree ht), mul_one]
    _ = q.eval t⁻¹ * t ^ q.natDegree := by rw [h']
    _ = t ^ q.natDegree * q.eval t⁻¹ := mul_comm _ _

private lemma reciprocal_coeff_zero (p q : Polynomial k)
    (h : ∀ t : k, t ≠ 0 → q.eval t⁻¹ = t * p.eval t) : q.coeff 0 = 0 := by
  have heq : q.reflect q.natDegree = Polynomial.X ^ (q.natDegree + 1) * p := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_of_finite_compl
      (by simp : ({t : k | t ≠ 0} : Set k)ᶜ.Finite)).mono
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    rw [eval_reflect_natDegree q t ht, h t ht]
    simp [pow_succ, mul_assoc]
  have hc := congrArg (fun r : Polynomial k => r.coeff q.natDegree) heq
  simpa [Polynomial.coeff_reflect, Polynomial.revAt_le le_rfl,
    Polynomial.coeff_X_pow_mul'] using hc

variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private theorem root_fixed_coroot_one_eq_zero [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) (v : V)
    (hx : ∀ t, (ρ.action (S.chevalley.x α t)).val v = v)
    (hh : ∀ t : kˣ, (ρ.action (S.chevalley.h α t)).val v = (t : k) • v) :
    v = 0 := by
  by_contra hv
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hv
  let w := (ρ.action (S.chevalley.n α 1)).val v
  let p := curvePolynomial ρ hρ (rootMorphism S α) l w
  let q := curvePolynomial ρ hρ (rootMorphism S (S.roots.neg α)) l v
  have hp (t : k) : p.eval t = l ((ρ.action (S.chevalley.x α t)).val w) := by
    rw [curvePolynomial_eval, rootMorphism_apply]
  have hq (t : k) : q.eval t =
      l ((ρ.action (S.chevalley.x (S.roots.neg α) t)).val v) := by
    rw [curvePolynomial_eval, rootMorphism_apply]
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
  have hpq (t : k) (ht : t ≠ 0) : q.eval t⁻¹ = t * p.eval t := by
    have hw := hword (Units.mk0 t ht)
    simp only [Units.val_mk0] at hw
    rw [hq, hp, hw, map_mul, map_mul, map_mul]
    change l ((ρ.action _).val ((ρ.action _).val ((ρ.action _).val
      ((ρ.action _).val v)))) = _
    rw [hx, hh, map_smul, map_smul, map_smul]
    rfl
  have hc := reciprocal_coeff_zero p q hpq
  have hc0 : q.coeff 0 = 1 := by
    rw [curvePolynomial_coeff_zero, hl]
  exact one_ne_zero (hc0.symm.trans hc)

open Theory.AlgebraicGroup.StandardRootSystem
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

private theorem basic_highWeight_coefficient_false [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (a : BasicWeight) (v : V)
    (hv : HasHighWeight ρ S.borel S.torus v (S.weightEmbedding (coefficient a)))
    (i : Fin 4) : a i = false := by
  cases ha : a i with
  | false => rfl
  | true =>
    exfalso
    apply hv.1.1
    let α := S.rootEquiv.symm (typeDSimpleRootIndex 2 i)
    have hsimple : α ∈ S.roots.simple := by
      apply (S.based.2.2.2.1 α).mpr
      simpa only [α, Equiv.apply_symm_apply, ← typeDRootPairing_baseEquiv_val] using
        (typeDRootPairing_baseEquiv 2 i).property
    have hpos : α ∈ S.roots.positive :=
      ((S.realized.2.2.2.2.2.2.2.2.2.2.2.1 α).mp hsimple).1
    let B := S.bigCell.data.positive_witness
    have hfix := invariantLine_fixed_of_unipotent_subgroup ρ hρ S.borel B.unipotent
      v hv.1 B.radical.1 B.radical.2.1
    apply root_fixed_coroot_one_eq_zero S ρ hρ α v
    · intro t
      apply hfix
      change S.chevalley.x α t ∈ B.unipotent.toSubgroup
      rw [B.root_generated]
      apply rootSubgroup_le_RootSubgroupGenerated S.roots hpos
      change S.chevalley.x α t ∈ (S.roots.rootSubgroup α : Set (Variety.Point K))
      rw [← (S.chevalley_spec.1 α).2]
      exact ⟨t, rfl⟩
    · intro t
      let z : Variety.Point (KMult k) := (dPointEquiv 1).symm (fun _ => t)
      have hz : dPointEquiv 1 z 0 = t := by simp [z]
      have hh := hv.2.2 ((S.roots.rootCocharacter α).onPoints z)
      rw [S.coroot_spec, hz] at hh
      rw [S.weightEmbedding_coroot (coefficient a) i z] at hh
      simpa only [hz, coefficient, ha, Bool.true_eq, ↓reduceIte, zpow_one] using hh

/-- With the currently published Borel and character coordinates, a basic
highest weight must be zero. This is a convention obstruction, not a proof of
restricted infinitesimal simplicity. No irreducibility hypothesis is needed. -/
theorem basic_highWeight_eq_zero [CharP k 2] (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (a : BasicWeight)
    (hv : ∃ v, HasHighWeight ρ S.borel S.torus v
      (S.weightEmbedding (coefficient a))) : a = fun _ => false := by
  obtain ⟨v, hv⟩ := hv
  funext i
  exact basic_highWeight_coefficient_false S ρ hρ a v hv i

end
end RootDensityConventions
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
