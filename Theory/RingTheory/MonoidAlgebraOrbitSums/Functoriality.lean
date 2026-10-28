module

public import Theory.RingTheory.MonoidAlgebraOrbitSums
public import Mathlib.Algebra.CharP.Lemmas
/-!
# Orbit-sum functoriality and Frobenius

Distinct lattice-orbit sums are unchanged by reindexing through an injective
orbit-preserving lattice homomorphism. In a torsion-free lattice this applies
to multiplication by powers of the characteristic, giving Frobenius on values.
Point evaluations related by the actual group action give equal orbit sums.

Source: Steinberg (1963), §12.2, character relations under exceptional maps.
-/

public noncomputable section
open scoped BigOperators
open Classical
open Theory.PermutationBasisOrbitSums
namespace Theory.MonoidAlgebraOrbitSums
variable {F G L : Type*} [Field F] [Group G] [Finite G] [CommGroup L]
  [MulDistribMulAction G L]

lemma orbitSumValue_eq_sum (t : L →* Fˣ) (a : L) :
    orbitSumValue (G := G) t a =
      ∑ b ∈ (Finite.finite_mulAction_orbit (M := G) a).toFinset, (t b : F) := by
  unfold orbitSumValue orbitSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact pointEvaluation_basis t b

lemma orbitSumValue_eq_of_point_equiv (t s : L →* Fˣ) (w : G)
    (heq : ∀ a, s a = t (w • a)) (a : L) :
    orbitSumValue (G := G) s a = orbitSumValue (G := G) t a := by
  rw [orbitSumValue_eq_sum, orbitSumValue_eq_sum]
  apply Finset.sum_bij (fun b _ => w • b)
  · intro b hb
    simpa only [Set.Finite.mem_toFinset] using
      (orbit_mem_smul_iff a b w).mpr (by simpa only [Set.Finite.mem_toFinset] using hb)
  · intro b hb c hc he
    exact (MulAction.injective w) he
  · intro b hb
    refine ⟨w⁻¹ • b, ?_, smul_inv_smul w b⟩
    simpa only [Set.Finite.mem_toFinset] using
      (orbit_mem_smul_iff a b w⁻¹).mpr (by simpa only [Set.Finite.mem_toFinset] using hb)
  · intro b hb
    exact congrArg Units.val (heq b)

lemma orbitSumValue_comp (t : L →* Fˣ) (ψ : L →* L)
    (hψ : Function.Injective ψ) (a : L)
    (horbit : ψ '' MulAction.orbit G a = MulAction.orbit G (ψ a)) :
    orbitSumValue (G := G) (t.comp ψ) a = orbitSumValue (G := G) t (ψ a) := by
  have hset : (Finite.finite_mulAction_orbit (M := G) (ψ a)).toFinset =
      (Finite.finite_mulAction_orbit (M := G) a).toFinset.image ψ := by
    apply Finset.coe_injective
    simp only [Set.Finite.coe_toFinset, Finset.coe_image]
    exact horbit.symm
  rw [orbitSumValue_eq_sum, orbitSumValue_eq_sum, hset, Finset.sum_image]
  · rfl
  · exact fun _ _ _ _ h => hψ h

lemma orbitSumValue_frobenius [CharP F 2] [IsMulTorsionFree L]
    (t : L →* Fˣ) (a : L) (n : ℕ) :
    orbitSumValue (G := G) t (a ^ (2 ^ n)) = (orbitSumValue (G := G) t a) ^ (2 ^ n) := by
  let ψ : L →* L := powMonoidHom (2 ^ n)
  have hinj : Function.Injective ψ := pow_left_injective (by positivity)
  have horbit : ψ '' MulAction.orbit G a = MulAction.orbit G (ψ a) := by
    ext b
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨g, ?_⟩
      exact (map_pow (MulDistribMulAction.toMulAut G L g) a (2 ^ n))
    · rintro ⟨g, rfl⟩
      refine ⟨g • a, ⟨g, rfl⟩, ?_⟩
      exact (map_pow (MulDistribMulAction.toMulAut G L g) a (2 ^ n)).symm
  change orbitSumValue (G := G) t (ψ a) = (orbitSumValue (G := G) t a) ^ (2 ^ n)
  rw [← orbitSumValue_comp t ψ hinj a horbit, orbitSumValue_eq_sum,
    orbitSumValue_eq_sum, sum_pow_char_pow]
  apply Finset.sum_congr rfl
  intro b _
  simp only [MonoidHom.comp_apply, ψ, powMonoidHom_apply, map_pow, Units.val_pow_eq_pow_val]
end Theory.MonoidAlgebraOrbitSums
