module

public import Theory.Character.ModularBlock.BlockConjugationTrace

/-!
# Mixed traces of an ordinary block

The trace of left multiplication by `a` and right multiplication by `b⁻¹`
on a complex block ideal is the inner product of its character columns at
`a` and `b`. Schur averaging gives the formula directly in the group basis.
This is the ordinary-character input for mixed Brauer trace comparisons.

Source: the usual block column orthogonality argument, as in Fong,
*Some Sylow subgroups of order 32 and a characterization of U(3,3)* (1967),
p. 71; the conjugation case is in `BlockConjugationTrace`.
-/

public section
noncomputable section

namespace ModularBlock.MixedConjugationTrace

open scoped BigOperators
open PrincipalBlockConstruction BlockOrthogonality
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

/-- Left and inverse right multiplication, followed by the block projection. -/
@[expose] def projectedLeftRight {R : Type*} [CommRing R]
    (e : MonoidAlgebra R G) (a b : G) :
    Module.End R (MonoidAlgebra R G) :=
  (LinearMap.mulLeft R (MonoidAlgebra.of R G a)).comp
    ((LinearMap.mulRight R (MonoidAlgebra.of R G b⁻¹)).comp
      (LinearMap.mulRight R e))

/-- The diagonal coefficients of projected left and right multiplication in the group basis. -/
theorem trace_projectedLeftRight {R : Type*} [CommRing R]
    (e : MonoidAlgebra R G) (a b : G) :
    LinearMap.trace R (MonoidAlgebra R G) (projectedLeftRight e a b) =
      ∑ x : G, e.coeff (x⁻¹ * a⁻¹ * x * b) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R (MonoidAlgebra.basis G R), Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, projectedLeftRight,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  change (MonoidAlgebra.single a 1 *
    ((MonoidAlgebra.single x 1 * e) * MonoidAlgebra.single b⁻¹ 1)).coeff x = _
  simp [MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, mul_assoc]

private def conjugateSum (y : G) : MonoidAlgebra ℂ G :=
  ∑ x : G, MonoidAlgebra.single (x * y * x⁻¹) 1

private theorem conjugateSum_comm (y : G) (a : MonoidAlgebra ℂ G) :
    a * conjugateSum y = conjugateSum y * a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_mul, mul_add, ha, hb]
  | single g r =>
    simp only [conjugateSum, Finset.mul_sum, Finset.sum_mul,
      MonoidAlgebra.single_mul_single, mul_one, one_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun x => by simp [mul_assoc])

/-- Schur averaging, with the degree multiplied through to avoid division. -/
theorem degree_mul_sum_character_mixed
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho] (a b : G) :
    rho.character 1 * (∑ x : G, rho.character (b⁻¹ * x⁻¹ * a * x)) =
      (Nat.card G : ℂ) * (rho.character a * star (rho.character b)) := by
  classical
  obtain ⟨c, hc⟩ := centralElementIntertwiner_eq_scalar rho (conjugateSum a)
    (conjugateSum_comm a)
  have hsum : rho.asAlgebraHom (conjugateSum a) =
      ∑ x : G, rho (x * a * x⁻¹) := by
    simp [conjugateSum]
  have htrace : (Nat.card G : ℂ) * rho.character a = c * rho.character 1 := by
    have h := congrArg (LinearMap.trace ℂ V) hc
    rw [hsum, map_sum, map_smul] at h
    change (∑ x : G, rho.character (x * a * x⁻¹)) =
      c * LinearMap.trace ℂ V 1 at h
    have hone : LinearMap.trace ℂ V 1 = rho.character 1 := by
      simp [Representation.character]
    rw [hone] at h
    simpa only [Representation.char_conj, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_eq_nat_card] using h
  have hproduct : (∑ x : G, rho.character (b⁻¹ * (x * a * x⁻¹))) =
      c * rho.character b⁻¹ := by
    have h := congrArg (fun f => LinearMap.trace ℂ V (rho b⁻¹ * f)) hc
    rw [hsum] at h
    simpa [Finset.mul_sum, map_sum, ← map_mul, Algebra.mul_smul_comm,
      map_smul, Representation.character] using h
  have hinv : (∑ x : G, rho.character (b⁻¹ * x⁻¹ * a * x)) =
      ∑ x : G, rho.character (b⁻¹ * (x * a * x⁻¹)) := by
    simpa only [Equiv.inv_apply, mul_assoc, inv_inv] using
      Equiv.sum_comp (Equiv.inv G) (fun x => rho.character (b⁻¹ * (x * a * x⁻¹)))
  rw [hinv, hproduct, Representation.representation_character_inv_eq_star_character]
  calc
    _ = (c * rho.character 1) * star (rho.character b) := by ring
    _ = _ := by rw [← htrace]; ring

/-- The mixed block trace is the inner product of its ordinary character columns. -/
theorem principalBlock_leftRight_trace
    (d : PrincipalCongruenceBlockData G) (a b : G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (projectedLeftRight (principalBlockElement d) a b) =
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk a) *
        star (d.chi i (ConjClasses.mk b)) := by
  classical
  rw [trace_projectedLeftRight]
  simp_rw [principalBlockElement_coeff]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hchar (i : d.I) :
      (∑ x : G, d.chi i (ConjClasses.mk (1 : G)) *
        d.chi i (ConjClasses.mk (x⁻¹ * a⁻¹ * x * b)⁻¹)) =
      (Nat.card G : ℂ) * (d.chi i (ConjClasses.mk a) *
        star (d.chi i (ConjClasses.mk b))) := by
    obtain ⟨n, rho, hrho⟩ := (d.complete.1 i).1
    let : Representation.IsIrreducible rho :=
      (irreducible_iff_character_norm_one (ρ := rho)).mpr
        (by simpa only [← hrho] using (d.complete.1 i).2)
    rw [hrho, ← Finset.mul_sum]
    change rho.character 1 * (∑ x : G, rho.character (x⁻¹ * a⁻¹ * x * b)⁻¹) =
      (Nat.card G : ℂ) * (rho.character a * star (rho.character b))
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using
      degree_mul_sum_character_mixed rho a b
  simp_rw [hchar]
  rw [← Finset.mul_sum]
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end ModularBlock.MixedConjugationTrace
