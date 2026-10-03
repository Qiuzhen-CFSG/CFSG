module

public import Theory.Character.ModularBlock.CharacterProjectorDefs

/-!
# Scaled idempotence of integral character projectors

An irreducible character's numerator projector acts by the group order on
that irreducible and by zero on all others. Schur's lemma first gives a
scalar action; traces and character orthogonality identify the scalar.
Reconstruction of central coefficients from a complete family of scalar
actions then proves `q * q = |G| smul q` over the complex numbers.
The injective coefficient map descends this relation to the cyclotomic
localization. These are the integral scaled projectors whose right ideals
form the isotypic lattices used in the modular argument.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/IsotypicLattice.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.IsotypicLattice

universe u v

attribute [local instance] Fintype.ofFinite

open PrincipalBlockConstruction

section CharacterProjector

variable {G : Type u} [Group G] [Finite G]

private theorem star_character_eq_inv
    (d : PrincipalCongruenceBlockData G) (i : d.I) (g : G) :
    star (d.chi i (ConjClasses.mk g)) =
      d.chi i (ConjClasses.mk g⁻¹) := by
  rcases (d.complete.1 i).1 with ⟨n, rho, hrho⟩
  rw [hrho]
  exact (Representation.representation_character_inv_eq_star_character
    rho g).symm

/-- The numerator projector acts by `|G|` on its chosen irreducible and by
zero on every other irreducible. -/
theorem complexCharacterProjectorNumerator_action
    (d : PrincipalCongruenceBlockData G) (i j : d.I)
    {n : ℕ} (rho : Representation ℂ G (Fin n → ℂ))
    (hrho : d.chi j = (characterClassFunction rho)) :
    rho.asAlgebraHom (complexCharacterProjectorNumerator d i) =
      (if i = j then (Nat.card G : ℂ) else 0) •
        (1 : Module.End ℂ (Fin n → ℂ)) := by
  classical
  have hirr : Representation.IsIrreducible rho := by
    apply (irreducible_iff_character_norm_one (ρ := rho)).2
    simpa [← hrho] using (d.complete.1 j).2
  let : Representation.IsIrreducible rho := hirr
  let q := complexCharacterProjectorNumerator d i
  have hqcenter : q ∈ Set.center (MonoidAlgebra ℂ G) :=
    complexCharacterProjectorNumerator_mem_center d i
  obtain ⟨lambda, hlambda⟩ := centralElementIntertwiner_eq_scalar rho q
    (Semigroup.mem_center_iff.mp hqcenter)
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hinner := completeFamily_inner d.chi d.complete j i
  rw [classFunctionInner] at hinner
  simp_rw [star_character_eq_inv d i] at hinner
  have hsum :
      ∑ g : G,
          d.chi j (ConjClasses.mk g) *
            d.chi i (ConjClasses.mk g⁻¹) =
        (Nat.card G : ℂ) * (if j = i then 1 else 0) := by
    apply (mul_left_cancel₀ hcard)
    calc
      (Nat.card G : ℂ) *
          ∑ g : G,
            d.chi j (ConjClasses.mk g) *
              d.chi i (ConjClasses.mk g⁻¹) =
          (Nat.card G : ℂ) ^ 2 *
            ((Nat.card G : ℂ)⁻¹ *
              ∑ g : G,
                d.chi j (ConjClasses.mk g) *
                  d.chi i (ConjClasses.mk g⁻¹)) := by
            field_simp [hcard]
      _ = (Nat.card G : ℂ) ^ 2 *
          (if j = i then 1 else 0) := by rw [hinner]
      _ = (Nat.card G : ℂ) *
          ((Nat.card G : ℂ) * (if j = i then 1 else 0)) := by ring
  have htraceQ :
      LinearMap.trace ℂ (Fin n → ℂ) (rho.asAlgebraHom q) =
        d.chi i (ConjClasses.mk (1 : G)) *
          ((Nat.card G : ℂ) * (if j = i then 1 else 0)) := by
    rw [groupAlgebra_trace]
    change (∑ g : G,
        (complexCharacterProjectorNumerator d i).coeff g * rho.character g) = _
    simp_rw [complexCharacterProjectorNumerator_apply]
    have hchar (g : G) : rho.character g =
        d.chi j (ConjClasses.mk g) := by
      rw [hrho]
      rfl
    simp_rw [hchar]
    calc
      (∑ g : G,
          d.chi i (ConjClasses.mk (1 : G)) *
            d.chi i (ConjClasses.mk g⁻¹) *
              d.chi j (ConjClasses.mk g)) =
          d.chi i (ConjClasses.mk (1 : G)) *
            ∑ g : G,
              d.chi j (ConjClasses.mk g) *
                d.chi i (ConjClasses.mk g⁻¹) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro g _
            ring
      _ = d.chi i (ConjClasses.mk (1 : G)) *
          ((Nat.card G : ℂ) * (if j = i then 1 else 0)) := by
            rw [hsum]
  have hdegree : d.chi j (ConjClasses.mk (1 : G)) = (n : ℂ) := by
    rw [hrho]
    change rho.character 1 = (n : ℂ)
    simp [Representation.character]
  have hn : (n : ℂ) ≠ 0 := by
    have hpos : 0 < n := by
      have : Nontrivial (Fin n → ℂ) :=
        irreducible_nontrivial (ρ := rho)
      simpa using
        ((Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2
          inferInstance)
    exact_mod_cast hpos.ne'
  rw [hlambda] at htraceQ
  simp only [map_smul, LinearMap.trace_one, smul_eq_mul] at htraceQ
  have hfinrank : Module.finrank ℂ (Fin n → ℂ) = n := by simp
  rw [hfinrank] at htraceQ
  by_cases hij : i = j
  · subst j
    rw [hdegree] at htraceQ
    have hlambda_eq : lambda = (Nat.card G : ℂ) := by
      apply (mul_right_cancel₀ hn)
      simpa [mul_comm, mul_assoc] using htraceQ
    simpa [hlambda_eq] using hlambda
  · have hji : j ≠ i := Ne.symm hij
    simp only [if_neg hji, mul_zero] at htraceQ
    have hlambda0 : lambda = 0 := by
      apply (mul_right_cancel₀ hn)
      simpa using htraceQ
    simpa [q, hij, hlambda0] using hlambda

/-- The denominator-cleared primitive character projector satisfies the
scaled idempotence relation `q² = |G| q` over `ℂ`. -/
theorem complexCharacterProjectorNumerator_mul_self
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    complexCharacterProjectorNumerator d i *
        complexCharacterProjectorNumerator d i =
      (Nat.card G : ℂ) • complexCharacterProjectorNumerator d i := by
  classical
  let q := complexCharacterProjectorNumerator d i
  have hqcenter : q ∈ Set.center (MonoidAlgebra ℂ G) :=
    complexCharacterProjectorNumerator_mem_center d i
  let qz : Subring.center (MonoidAlgebra ℂ G) := ⟨q, hqcenter⟩
  let zz : Subring.center (MonoidAlgebra ℂ G) :=
    qz * qz - (Nat.card G : Subring.center (MonoidAlgebra ℂ G)) * qz
  let z : MonoidAlgebra ℂ G := zz.1
  have hzcenter : z ∈ Set.center (MonoidAlgebra ℂ G) := zz.property
  have hz_expand : z = q * q - (Nat.card G : ℂ) • q := by
    simp [z, zz, qz, Algebra.smul_def]
  have haction (j : d.I) {n : ℕ}
      (rho : Representation ℂ G (Fin n → ℂ))
      (hrho : d.chi j = (characterClassFunction rho)) :
      rho.asAlgebraHom z =
        (0 : ℂ) • (1 : Module.End ℂ (Fin n → ℂ)) := by
    rw [hz_expand, map_sub, map_mul, map_smul]
    rw [complexCharacterProjectorNumerator_action d i j rho hrho]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  have hzcoeff (g : G) : z.coeff g = 0 := by
    have hcoeff :=
      BlockOrthogonality.coeff_eq_inv_card_mul_sum_scalar_degree_character
        d.chi d.complete z (Semigroup.mem_center_iff.mp hzcenter)
        (fun _ ↦ (0 : ℂ)) (by
          intro j n rho hrho
          exact haction j rho hrho) g
    simpa using hcoeff
  have hzzero : z = 0 := by
    ext g
    exact hzcoeff g
  rw [hz_expand] at hzzero
  exact sub_eq_zero.mp hzzero

/-- The integral numerator projector already satisfies `q² = |G| q` in
the localized cyclotomic group algebra. -/
theorem characterProjectorNumerator_mul_self
    (d : PrincipalCongruenceBlockData G) (i : d.I) :
    characterProjectorNumerator d i * characterProjectorNumerator d i =
      (Nat.card G : Localization.AtPrime d.primeIdeal) •
        characterProjectorNumerator d i := by
  classical
  apply mapRingHom_injective (localizationToComplex d)
    (localizationToComplex_injective d)
  rw [map_mul, map_characterProjectorNumerator,
    complexCharacterProjectorNumerator_mul_self]
  ext g
  simp [MonoidAlgebra.coeff_mapRingHom]

end CharacterProjector

end ModularBlock.IsotypicLattice

