module

public import Theory.Character.ModularBlock.PrincipalElement

/-!
# The conjugation trace of an ordinary block

The conjugation character of a complex block ideal is the sum of the squared
absolute values of its ordinary irreducible characters. We compute the trace
in the group basis, then use Schur's lemma on the sum of all conjugates of a
group element. At the identity this gives the sum of squared degrees.

This is the characteristic-zero side of local column orthogonality. Its
modular counterpart identifies this conjugation trace at a two-element with
the dimension of the Brauer image. The intended application is Fong,
*Some Sylow subgroups of order 32 and a characterization of U(3,3)*,
J. Algebra 6 (1967), p. 71, equation (6).
-/

public section
noncomputable section

namespace ModularBlock.BlockConjugationTrace

open scoped BigOperators
open PrincipalBlockConstruction BlockOrthogonality
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

/-- Conjugation by a group element, followed by the block projection. -/
@[expose] def projectedConjugation {R : Type*} [CommRing R]
    (e : MonoidAlgebra R G) (y : G) :
    Module.End R (MonoidAlgebra R G) :=
  (LinearMap.mulLeft R (MonoidAlgebra.of R G y)).comp
    ((LinearMap.mulRight R (MonoidAlgebra.of R G y⁻¹)).comp
      (LinearMap.mulRight R e))

/-- The diagonal coefficients of projected conjugation in the group basis. -/
theorem trace_projectedConjugation {R : Type*} [CommRing R]
    (e : MonoidAlgebra R G) (y : G) :
    LinearMap.trace R (MonoidAlgebra R G) (projectedConjugation e y) =
      ∑ x : G, e.coeff (x⁻¹ * y⁻¹ * x * y) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R (MonoidAlgebra.basis G R), Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, projectedConjugation,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  change (MonoidAlgebra.single y 1 *
    ((MonoidAlgebra.single x 1 * e) * MonoidAlgebra.single y⁻¹ 1)).coeff x = _
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
theorem degree_mul_sum_character_commutator
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho] (y : G) :
    rho.character 1 * (∑ x : G, rho.character (y⁻¹ * x⁻¹ * y * x)) =
      (Nat.card G : ℂ) * (rho.character y * star (rho.character y)) := by
  classical
  obtain ⟨a, ha⟩ := centralElementIntertwiner_eq_scalar rho (conjugateSum y)
    (conjugateSum_comm y)
  have hsum : rho.asAlgebraHom (conjugateSum y) =
      ∑ x : G, rho (x * y * x⁻¹) := by
    simp [conjugateSum]
  have htrace : (Nat.card G : ℂ) * rho.character y = a * rho.character 1 := by
    have h := congrArg (LinearMap.trace ℂ V) ha
    rw [hsum, map_sum, map_smul] at h
    change (∑ x : G, rho.character (x * y * x⁻¹)) =
      a * LinearMap.trace ℂ V 1 at h
    have hone : LinearMap.trace ℂ V 1 = rho.character 1 := by
      simp [Representation.character]
    rw [hone] at h
    simpa only [Representation.char_conj, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_eq_nat_card] using h
  have hproduct : (∑ x : G, rho.character (y⁻¹ * (x * y * x⁻¹))) =
      a * rho.character y⁻¹ := by
    have h := congrArg (fun f => LinearMap.trace ℂ V (rho y⁻¹ * f)) ha
    rw [hsum] at h
    simpa [Finset.mul_sum, map_sum, ← map_mul, Algebra.mul_smul_comm,
      map_smul, Representation.character] using h
  have hinv : (∑ x : G, rho.character (y⁻¹ * x⁻¹ * y * x)) =
      ∑ x : G, rho.character (y⁻¹ * (x * y * x⁻¹)) := by
    simpa only [Equiv.inv_apply, mul_assoc, inv_inv] using
      Equiv.sum_comp (Equiv.inv G) (fun x => rho.character (y⁻¹ * (x * y * x⁻¹)))
  rw [hinv, hproduct, Representation.representation_character_inv_eq_star_character]
  calc
    _ = (a * rho.character 1) * star (rho.character y) := by ring
    _ = _ := by rw [← htrace]; ring

/-- The block's conjugation trace is its ordinary character column norm. -/
theorem principalBlock_conjugation_trace
    (d : PrincipalCongruenceBlockData G) (y : G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (projectedConjugation (principalBlockElement d) y) =
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk y) *
        star (d.chi i (ConjClasses.mk y)) := by
  classical
  rw [trace_projectedConjugation]
  simp_rw [principalBlockElement_coeff]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hchar (i : d.I) :
      (∑ x : G, d.chi i (ConjClasses.mk (1 : G)) *
        d.chi i (ConjClasses.mk (x⁻¹ * y⁻¹ * x * y)⁻¹)) =
      (Nat.card G : ℂ) * (d.chi i (ConjClasses.mk y) *
        star (d.chi i (ConjClasses.mk y))) := by
    obtain ⟨n, rho, hrho⟩ := (d.complete.1 i).1
    let : Representation.IsIrreducible rho :=
      (irreducible_iff_character_norm_one (ρ := rho)).mpr
        (by simpa only [← hrho] using (d.complete.1 i).2)
    rw [hrho, ← Finset.mul_sum]
    change rho.character 1 * (∑ x : G, rho.character (x⁻¹ * y⁻¹ * x * y)⁻¹) =
      (Nat.card G : ℂ) * (rho.character y * star (rho.character y))
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using
      degree_mul_sum_character_commutator rho y
  simp_rw [hchar]
  rw [← Finset.mul_sum]
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- The regular block projection has trace equal to the sum of squared degrees. -/
theorem principalBlock_projection_trace
    (d : PrincipalCongruenceBlockData G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (LinearMap.mulRight ℂ (principalBlockElement d)) =
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk (1 : G)) ^ 2 := by
  have h := principalBlock_conjugation_trace d (1 : G)
  have hstar (i : d.I) : star (d.chi i (ConjClasses.mk (1 : G))) =
      d.chi i (ConjClasses.mk (1 : G)) := by
    obtain ⟨n, rho, hrho⟩ := (d.complete.1 i).1
    rw [hrho]
    change star (rho.character 1) = rho.character 1
    simp [Representation.character]
  simpa only [projectedConjugation, inv_one, map_one, LinearMap.mulLeft_one,
    LinearMap.mulRight_one, LinearMap.id_comp, hstar, pow_two] using h

end ModularBlock.BlockConjugationTrace
