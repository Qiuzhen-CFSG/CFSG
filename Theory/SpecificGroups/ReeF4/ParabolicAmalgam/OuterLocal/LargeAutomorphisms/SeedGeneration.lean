module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation.Splitting
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.FullLeviRepresentation.Splitting
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.FixedBruhat

/-!
# Generation by the two actual Ree root seeds

The paired end and middle coroot words have long simple-root characters
`(a², a⁻¹)` and `(b⁻¹, b² / θ(b)²)`. These two families generate the entire
fixed torus: the identity `θ(θ(t))² = t` gives an explicit inverse to the
remaining character map `a ↦ a³ / θ(a)⁴`. The fixed positive subgroup and
both relative Weyl representatives already belong to the join of the seeds.
The proved fixed Bruhat factorization therefore makes this join the whole
fixed group, without a simplicity hypothesis.

This supplies fixed-seed generation for the two-power automorphism argument
in `LargeAutomorphisms`. Both subgroup memberships are transported through
the actual subsystem Levi inclusions and their matrix-preserving comparison.
No assertion that fixed points preserve arbitrary generated subgroups is used.
The result also holds for the full binary fixed group.

Source: GLS3, Sections 2.3--2.4 and 2.6.5(f),
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher--Smith, F.1.12(I)(5) and (II),
printed pp.263--264 of `refs/quasithin.pdf`.
-/

public section

namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms

open LargeLocalSeeds ConverseParabolics
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery

private theorem torus_relation {A : Type*} [CommGroup A] (a c x y : A) :
    a⁻¹ * ((a ^ 2 * c⁻¹) ^ 2 * ((x ^ 2 * y⁻¹) ^ 2)⁻¹) =
      (a ^ 3 * (x ^ 4)⁻¹) * (c ^ 2)⁻¹ * y ^ 2 := by
  simp only [mul_pow, mul_inv, inv_pow, inv_inv, ← pow_mul]
  norm_num only [Nat.reduceMul]
  calc
    _ = (a⁻¹ * a ^ 4) * (x ^ 4)⁻¹ * (c ^ 2)⁻¹ * y ^ 2 := by
      simp only [mul_assoc, mul_comm, mul_left_comm]
    _ = _ := by rw [show a⁻¹ * a ^ 4 = a ^ 3 by group]

private theorem theta_units_twice (m : ℕ) (a : (CoefficientField m)ˣ) :
    Units.map (theta m : CoefficientField m →* CoefficientField m)
      (Units.map (theta m : CoefficientField m →* CoefficientField m) a) ^ 2 = a := by
  apply Units.ext
  change (theta m (theta m a.val)) ^ 2 = a.val
  simp only [theta_apply, ← pow_mul, ← pow_add]
  rw [show 2 ^ (m + m) * 2 = 2 ^ (2 * m + 1) by
    rw [pow_succ]; congr 2; omega]
  exact field_pow m a.val

private theorem torus_parameter_surjective (m : ℕ) :
    Function.Surjective (fun a : (CoefficientField m)ˣ =>
      a ^ 3 * (Units.map (theta m : CoefficientField m →* CoefficientField m) a ^ 4)⁻¹) := by
  intro t
  refine ⟨t ^ 3 * Units.map (theta m : CoefficientField m →* CoefficientField m) t ^ 4, ?_⟩
  simp only [map_mul, map_pow, mul_pow, ← pow_mul]
  have hθ : Units.map (theta m : CoefficientField m →* CoefficientField m)
      (Units.map (theta m : CoefficientField m →* CoefficientField m) t) ^ (4 * 4) = t ^ 8 := by
    rw [show 4 * 4 = 2 * 8 from rfl, pow_mul, theta_units_twice]
  rw [hθ]
  norm_num
  rw [show t ^ 9 = t * t ^ 8 by group]
  simp [mul_assoc, mul_comm, mul_left_comm]

private theorem torus_coordinates_surjective (m : ℕ)
    (c d : (CoefficientField m)ˣ) :
    ∃ a b : (CoefficientField m)ˣ,
      a ^ 2 * b⁻¹ = c ∧
      a⁻¹ * SuzukiFullLeviRepresentation.internalCharacter b = d := by
  obtain ⟨a, ha⟩ := torus_parameter_surjective m
    (d * c ^ 2 * (Units.map (theta m : CoefficientField m →* CoefficientField m) c ^ 2)⁻¹)
  dsimp only at ha
  let b := a ^ 2 * c⁻¹
  refine ⟨a, b, ?_, ?_⟩
  · simp [b, mul_left_comm]
  · have he : a⁻¹ * SuzukiFullLeviRepresentation.internalCharacter b =
        (a ^ 3 * (Units.map (theta m : CoefficientField m →* CoefficientField m) a ^ 4)⁻¹) *
          (c ^ 2)⁻¹ * Units.map (theta m : CoefficientField m →* CoefficientField m) c ^ 2 := by
      dsimp only [b, SuzukiFullLeviRepresentation.internalCharacter]
      rw [map_mul, map_pow, map_inv]
      exact torus_relation a c _ _
    rw [he, ha]
    simp [mul_assoc, mul_comm, mul_left_comm]

open Subgroup
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open FullLeviRepresentation

/-- Both actual subsystem tori together cover the full fixed torus. -/
theorem fixedTorus_le_seeds (m : ℕ) :
    fixedTorus m ≤ seed m .suzuki ⊔ seed m .linear := by
  intro x hx
  obtain ⟨c, d, rfl⟩ := exists_torusElement x hx
  obtain ⟨a, b, hc, hd⟩ := torus_coordinates_surjective m c d
  have he : torusElement c d =
      torusElement (a ^ 2) a⁻¹ *
        torusElement b⁻¹ (SuzukiFullLeviRepresentation.internalCharacter b) := by
    change torusHom m (c, d) = torusHom m (a ^ 2, a⁻¹) *
      torusHom m (b⁻¹, SuzukiFullLeviRepresentation.internalCharacter b)
    rw [← map_mul]
    congr 1
    exact Prod.ext hc.symm hd.symm
  rw [he]
  apply mul_mem
  · apply mem_sup_right
    have h := FullLeviRepresentation.internal_torus_mem a
    rw [FullLeviRepresentation.seedLeviHom_range] at h
    exact splitLevi_le_seed m .linear h
  · apply mem_sup_left
    have h := SuzukiFullLeviRepresentation.internal_torus_mem b
    rw [SuzukiFullLeviRepresentation.seedLeviHom_range] at h
    exact splitLevi_le_seed m .suzuki h

open SectionGeometry.BNPair
open Parabolics.Binary.FixedGeometry

/-- The root-defined Suzuki and linear seeds generate the actual fixed group,
without simplicity, perfectness, or a restriction on the parameter. -/
theorem seed_sup_eq_top (m : ℕ) : seed m .suzuki ⊔ seed m .linear = ⊤ := by
  have hT := fixedTorus_le_seeds m
  have hU : unipotent m ≤ seed m .suzuki ⊔ seed m .linear :=
    (unipotent_le_seed m .suzuki).trans le_sup_left
  have hB : borel m ≤ seed m .suzuki ⊔ seed m .linear := by
    rw [borel_eq_unipotent_sup_fixedTorus]
    exact sup_le hU hT
  have hN : normalizerWords m ≤ seed m .suzuki ⊔ seed m .linear :=
    (normalizerWords_le_fixedTorus_sup_weylSubgroup_of_monomial m
      (fun _ hn => Overlap.normalizerWords_weylMonomial
        (splitTorus_eq_diagonalTorus m) hn)
      (fun _ hn htri => Overlap.normalizerWord_mem_diagonalTorus_of_heightTriangular
        (splitTorus_eq_diagonalTorus m) hn htri)).trans
      (sup_le hT (weylSubgroup_le_seeds m))
  apply top_unique
  rw [← borel_sup_normalizerWords m]
  exact sup_le hB hN

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms
