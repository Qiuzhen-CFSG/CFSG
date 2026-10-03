module

public import Theory.Character.ModularBlock.PrincipalElement

/-!
# The ordinary block bimodule trace

Left multiplication by `g` and right multiplication by `h` on the complex
principal block algebra have trace `∑ χ, χ(g) χ(h)`. There is no conjugation
on the second character value. The group-basis calculation expresses the
trace as a sum of block-idempotent coefficients; Schur averaging computes
each character's contribution.

This is the two-variable version of `BlockConjugationTrace.lean`, and the
ordinary-character side of the central p-quotient comparison in Feit,
*The Representation Theory of Finite Groups*, IV.4.12.
-/

public section
noncomputable section
namespace ModularBlock.BlockBimoduleTrace
open scoped BigOperators
open PrincipalBlockConstruction BlockOrthogonality
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- Left and right multiplication after the block projection. -/
@[expose] def projectedBimultiplication {R : Type*} [CommRing R]
    (e : MonoidAlgebra R G) (g h : G) :
    Module.End R (MonoidAlgebra R G) :=
  (LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
    ((LinearMap.mulRight R (MonoidAlgebra.of R G h)).comp
      (LinearMap.mulRight R e))

/-- The diagonal coefficients in the group basis. -/
theorem trace_projectedBimultiplication {R : Type*} [CommRing R]
    (e : MonoidAlgebra R G) (g h : G) :
    LinearMap.trace R (MonoidAlgebra R G) (projectedBimultiplication e g h) =
      ∑ x : G, e.coeff (x⁻¹ * g⁻¹ * x * h⁻¹) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R (MonoidAlgebra.basis G R), Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, projectedBimultiplication,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  change (MonoidAlgebra.single g 1 *
    ((MonoidAlgebra.single x 1 * e) * MonoidAlgebra.single h 1)).coeff x = _
  simp [MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, mul_assoc]

/-- Two-sided projected traces commute with coefficient homomorphisms. -/
theorem map_trace_projectedBimultiplication {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (e : MonoidAlgebra R G) (g h : G) :
    f (LinearMap.trace R (MonoidAlgebra R G) (projectedBimultiplication e g h)) =
      LinearMap.trace S (MonoidAlgebra S G)
        (projectedBimultiplication (MonoidAlgebra.mapRingHom G f e) g h) := by
  classical
  rw [trace_projectedBimultiplication, trace_projectedBimultiplication, map_sum]
  rfl

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

/-- Schur averaging in two independent variables. -/
theorem degree_mul_sum_character_conjugate_mul
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho] (g h : G) :
    rho.character 1 * (∑ x : G, rho.character (h * x⁻¹ * g * x)) =
      (Nat.card G : ℂ) * (rho.character g * rho.character h) := by
  classical
  obtain ⟨a, ha⟩ := centralElementIntertwiner_eq_scalar rho (conjugateSum g)
    (conjugateSum_comm g)
  have hsum : rho.asAlgebraHom (conjugateSum g) =
      ∑ x : G, rho (x * g * x⁻¹) := by
    simp [conjugateSum]
  have htrace : (Nat.card G : ℂ) * rho.character g = a * rho.character 1 := by
    have h := congrArg (LinearMap.trace ℂ V) ha
    rw [hsum, map_sum, map_smul] at h
    change (∑ x : G, rho.character (x * g * x⁻¹)) =
      a * LinearMap.trace ℂ V 1 at h
    have hone : LinearMap.trace ℂ V 1 = rho.character 1 := by
      simp [Representation.character]
    rw [hone] at h
    simpa only [Representation.char_conj, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_eq_nat_card] using h
  have hproduct : (∑ x : G, rho.character (h * (x * g * x⁻¹))) =
      a * rho.character h := by
    have h := congrArg (fun f => LinearMap.trace ℂ V (rho h * f)) ha
    rw [hsum] at h
    simpa [Finset.mul_sum, map_sum, ← map_mul, Algebra.mul_smul_comm,
      map_smul, Representation.character] using h
  have hinv : (∑ x : G, rho.character (h * x⁻¹ * g * x)) =
      ∑ x : G, rho.character (h * (x * g * x⁻¹)) := by
    simpa only [Equiv.inv_apply, mul_assoc, inv_inv] using
      Equiv.sum_comp (Equiv.inv G) (fun x => rho.character (h * (x * g * x⁻¹)))
  rw [hinv, hproduct]
  calc
    _ = (a * rho.character 1) * rho.character h := by ring
    _ = _ := by rw [← htrace]; ring

/-- The ordinary block kernel is a two-sided multiplication trace. -/
theorem principalBlock_bimultiplication_trace
    (d : PrincipalCongruenceBlockData G) (g h : G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (projectedBimultiplication (principalBlockElement d) g h) =
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk g) *
        d.chi i (ConjClasses.mk h) := by
  classical
  rw [trace_projectedBimultiplication]
  simp_rw [principalBlockElement_coeff]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hchar (i : d.I) :
      (∑ x : G, d.chi i (ConjClasses.mk (1 : G)) *
        d.chi i (ConjClasses.mk (x⁻¹ * g⁻¹ * x * h⁻¹)⁻¹)) =
      (Nat.card G : ℂ) * (d.chi i (ConjClasses.mk g) *
        d.chi i (ConjClasses.mk h)) := by
    obtain ⟨n, rho, hrho⟩ := (d.complete.1 i).1
    let : Representation.IsIrreducible rho :=
      (irreducible_iff_character_norm_one (ρ := rho)).mpr
        (by simpa only [← hrho] using (d.complete.1 i).2)
    rw [hrho, ← Finset.mul_sum]
    change rho.character 1 * (∑ x : G, rho.character (x⁻¹ * g⁻¹ * x * h⁻¹)⁻¹) =
      (Nat.card G : ℂ) * (rho.character g * rho.character h)
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using
      degree_mul_sum_character_conjugate_mul rho g h
  simp_rw [hchar]
  rw [← Finset.mul_sum]
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end ModularBlock.BlockBimoduleTrace
