module

public import Theory.Character.ModularBlock.BrauerCharacterBasis
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# One-dimensional representations and genuine Brauer lifts

A multiplicative scalar character gives a simple one-dimensional module. Its
Brauer value is the lift of that scalar eigenvalue. Reduction followed by this
lift recovers any odd-order root in the datum's cyclotomic order. Conversely,
a scalar character of bounded odd exponent lifts multiplicatively through the
same coefficient map. These statements concern the actual eigenvalue lifts,
without a block-membership assumption.

This is the degree-one case of the Brauer-character construction used in
Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

public section
noncomputable section
namespace ModularBlock.BrauerLinearCharacters
open PrincipalBlockConstruction BrauerCoefficientExtension BrauerCharacter

/-- The scalar module associated to a field-valued homomorphism. -/
@[expose] def scalarRepresentation {F H : Type*} [Field F] [Group H]
    (χ : H →* F) : Representation F H (Fin 1 → F) where
  toFun g := χ g • (1 : Module.End F (Fin 1 → F))
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

theorem scalarRepresentation_irreducible {F H : Type*} [Field F] [Group H]
    (χ : H →* F) : Representation.IsIrreducible (scalarRepresentation χ) := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
  apply is_simple_module_of_finrank_eq_one (K := F)
  change Module.finrank F (Fin 1 → F) = 1
  simp

/-- In dimension one, the determinant is the scalar character of the module. -/
theorem equiv_scalarRepresentation_det {F H V : Type*} [Field F] [Group H]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F H V) (hdim : Module.finrank F V = 1) :
    Nonempty (ρ.Equiv (scalarRepresentation (LinearMap.det.comp ρ))) := by
  let e : V ≃ₗ[F] (Fin 1 → F) := LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  refine ⟨Representation.Equiv.mk e (fun g => ?_)⟩
  obtain ⟨a, ha, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
  have hdet : LinearMap.det (ρ g) = a := by
    rw [ha, LinearMap.det_smul, LinearMap.det_id, hdim, pow_one, mul_one]
  ext v i
  change e (ρ g v) i = (LinearMap.det (ρ g) • e v) i
  rw [hdet, ha]
  simp

variable {G : Type*} [Group G] [Finite G] (d : PrincipalCongruenceBlockData G)

theorem scalarRepresentation_value (χ : G →* splittingField d) (g : G) :
    value d (scalarRepresentation χ) g = (eigenvalueLift d (χ g) : ℂ) := by
  have hp : (scalarRepresentation χ g).charpoly = Polynomial.X - Polynomial.C (χ g) := by
    change (χ g • (1 : Module.End (splittingField d) (Fin 1 → splittingField d))).charpoly = _
    rw [← LinearMap.charpoly_toMatrix _ (Pi.basisFun (splittingField d) (Fin 1))]
    simp [Matrix.charpoly, Matrix.charmatrix]
  simp [value, integralValue, hp]

/-- Reduction followed by eigenvalue lifting fixes every admissible odd-order root. -/
theorem eigenvalueLift_reduction {n : ℕ} (hn : Odd n) (hdiv : n ∣ Nat.card G)
    (z : cyclotomicOrder d.eta) (hz : z ^ n = 1) :
    eigenvalueLift d (reduction d z) = z := by
  have hr : reduction d z ^ n = 1 := by rw [← map_pow, hz, map_one]
  rw [eigenvalueLift_eq_liftAtOrder d n hn hdiv _ hr]
  apply odd_root_eq_of_reduction_eq d hn hn hdiv hdiv
    (liftAtOrder_pow d n hn hdiv _ hr) hz
  exact reduction_liftAtOrder d n hn hdiv _ hr

/-- Multiplicative lifting of a scalar character of bounded odd exponent. -/
@[expose] def liftHom {H : Type*} [Group H] (χ : H →* splittingField d)
    (n : ℕ) (hn : Odd n) (hdiv : n ∣ Nat.card G) (hχ : ∀ g, χ g ^ n = 1) :
    H →* cyclotomicOrder d.eta where
  toFun g := liftAtOrder d n hn hdiv (χ g) (hχ g)
  map_one' := by
    apply odd_root_eq_of_reduction_eq d hn hn hdiv hdiv
      (liftAtOrder_pow d n hn hdiv _ (hχ 1)) (one_pow n)
    rw [reduction_liftAtOrder, map_one, map_one]
  map_mul' g h := by
    apply odd_root_eq_of_reduction_eq d hn hn hdiv hdiv
      (liftAtOrder_pow d n hn hdiv _ (hχ (g * h)))
    · rw [mul_pow, liftAtOrder_pow, liftAtOrder_pow, mul_one]
    · simp only [map_mul, reduction_liftAtOrder]

@[simp] theorem reduction_liftHom {H : Type*} [Group H] (χ : H →* splittingField d)
    (n : ℕ) (hn : Odd n) (hdiv : n ∣ Nat.card G) (hχ : ∀ g, χ g ^ n = 1) (g : H) :
    reduction d (liftHom d χ n hn hdiv hχ g) = χ g :=
  reduction_liftAtOrder d n hn hdiv (χ g) (hχ g)

end ModularBlock.BrauerLinearCharacters
