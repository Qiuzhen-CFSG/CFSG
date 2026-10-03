module

public import Theory.Character.DefectZeroProjector
public import Theory.Character.Divisibility

/-!
# Idempotence of ordinary irreducible character projectors

The normalized ordinary projector acts as the identity on a representation
with its character: centrality and Schur's lemma make the action scalar,
and self-orthogonality determines that scalar. The coefficient of a product
with the projector is a normalized trace, so this identity action implies
idempotence coefficient by coefficient. No complete character family or
block data is needed.

Source: the ordinary central-idempotent argument for defect-zero vanishing
used by Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)* (1967), pp. 74–75. The scalar-action step adapts the argument in
`Theory/Character/ModularBlock/CharacterProjector.lean`; the final trace
calculation uses only the given irreducible representation.
-/

public section
noncomputable section

open scoped BigOperators
open Representation
attribute [local instance] Fintype.ofFinite

namespace OrdinaryCharacter
variable {G : Type*} [Group G] [Finite G]

private theorem trace_action {n : ℕ}
    (ρ : Representation ℂ G (Fin n → ℂ)) (z : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ (Fin n → ℂ) (ρ.asAlgebraHom z) =
      ∑ g : G, z.coeff g * ρ.character g := by
  classical
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply,
    Finsupp.sum_fintype z.coeff (fun g r => r • ρ g)
      (fun g => zero_smul ℂ (ρ g))]
  simp only [map_sum, map_smul, smul_eq_mul, Representation.character]

private theorem projector_action {n : ℕ}
    (ρ : Representation ℂ G (Fin n → ℂ)) [ρ.IsIrreducible] :
    ρ.asAlgebraHom (projector ρ.character) = 1 := by
  classical
  obtain ⟨a, ha⟩ := centralElementIntertwiner_eq_scalar ρ
    (projector ρ.character)
    (Semigroup.mem_center_iff.mp (projector_mem_center (ρ.char_conj)))
  have hnorm := irreducibleCharacter_self (G := G) ⟨n, ρ, inferInstance, rfl⟩
  have htrace : LinearMap.trace ℂ (Fin n → ℂ)
      (ρ.asAlgebraHom (projector ρ.character)) = ρ.character 1 := by
    rw [trace_action]
    simp_rw [projector_coeff]
    calc
      (∑ g : G, (ρ.character 1 / (Nat.card G : ℂ) * ρ.character g⁻¹) *
          ρ.character g) = ρ.character 1 * characterProduct G ρ.character ρ.character := by
        simp only [characterProduct, div_eq_mul_inv, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        ring
      _ = ρ.character 1 := by rw [hnorm, mul_one]
  have hn : (n : ℂ) ≠ 0 := by
    have : Nontrivial (Fin n → ℂ) := irreducible_nontrivial ρ
    have hpos : 0 < n := by
      simpa using (Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2 inferInstance
    exact_mod_cast hpos.ne'
  rw [ha] at htrace
  have haone : a = 1 := by
    apply mul_right_cancel₀ hn
    simpa [Representation.character] using htrace
  simpa [haone] using ha

/-- Multiplication by the character projector is recovered from traces in
the given representation. -/
private theorem mul_projector_coeff {n : ℕ}
    (ρ : Representation ℂ G (Fin n → ℂ)) (z : MonoidAlgebra ℂ G) (g : G) :
    (z * projector ρ.character).coeff g =
      ρ.character 1 / (Nat.card G : ℂ) *
        LinearMap.trace ℂ (Fin n → ℂ) (ρ g⁻¹ * ρ.asAlgebraHom z) := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [add_mul, map_add, MonoidAlgebra.coeff_add, Finsupp.coe_add,
        Pi.add_apply, mul_add, hx, hy]
  | single h r =>
      simp only [MonoidAlgebra.coeff_single_mul_apply, projector_coeff,
        mul_inv_rev, inv_inv, Representation.asAlgebraHom_single,
        mul_smul_comm, map_smul, smul_eq_mul, ← map_mul]
      change r * (ρ.character 1 / (Nat.card G : ℂ) * ρ.character (g⁻¹ * h)) =
        ρ.character 1 / (Nat.card G : ℂ) * (r * ρ.character (g⁻¹ * h))
      ring

/-- The normalized projector of an ordinary irreducible character is
idempotent, independently of any block data. -/
theorem projector_isIdempotent {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    IsIdempotentElem (projector χ) := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  let := hρ
  change projector ρ.character * projector ρ.character = projector ρ.character
  ext g
  rw [mul_projector_coeff, projector_action, mul_one, projector_coeff]
  rfl
end OrdinaryCharacter
