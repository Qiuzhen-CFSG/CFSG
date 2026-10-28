module

public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.Transport
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.MarkingConjugacy.SwapCoordinates
public import Mathlib.GroupTheory.Sylow

/-!
# Simultaneous conjugacy of the source M₁₀ markings

Every source marking is obtained from the standard marking by one actual
permutation of the six letters, preserving the order of the two marked
transpositions. An order-nine subgroup of S₆ is Sylow, so Sylow conjugacy first
identifies its nine-group. Pulling back the two transpositions then reduces to
the eighteen normalizer conjugators checked in `SwapCoordinates`.

The argument uses only the marking's order, transposition and inversion
clauses. In particular, no elementary-abelian structure, distinctness or orbit
decomposition is assumed, and no fact about the full Aut(A₆) normalizer or
the extension M₁₀ is needed.

Source: M. Aschbacher, “A 2-local characterization of M12” (2003), the
markings in 4.8 and the local geometry in 4.9–4.10, pp.41–42.
-/

@[expose] public section

namespace AlternatingSix.M10.LocalGeometry
open Subgroup

namespace MarkingConjugacy

private def nineSylow (D : Subgroup (Equiv.Perm (Fin 6))) (hD : Nat.card D = 9) :
    Sylow 3 (Equiv.Perm (Fin 6)) :=
  Sylow.ofCard D (by
    rw [hD, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide +kernel)

private theorem subgroup_conjugacy (D : Subgroup (Equiv.Perm (Fin 6)))
    (hD : Nat.card D = 9) :
    ∃ σ : Equiv.Perm (Fin 6), standardNine.map (MulAut.conj σ).toMonoidHom = D := by
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 6))
    (nineSylow standardNine card_standardNine) (nineSylow D hD)
  exact ⟨σ, congrArg Sylow.toSubgroup hσ⟩

private theorem swap_conj (σ x : Equiv.Perm (Fin 6)) (hx : x.IsSwap) :
    ((MulAut.conj σ) x).IsSwap := by
  obtain ⟨a, b, hab, rfl⟩ := hx
  exact ⟨σ a, σ b, σ.injective.ne hab, (Equiv.swap_apply_apply σ a b).symm⟩

private theorem pullback_inverts (m : Marking) (σ : Equiv.Perm (Fin 6))
    (hσ : standardNine.map (MulAut.conj σ).toMonoidHom = m.D)
    (x : Equiv.Perm (Fin 6)) (hx : x ∈ standardNine) :
    let e := MulAut.conj σ
    (e.symm m.u * e.symm m.z) * x * (e.symm m.u * e.symm m.z)⁻¹ = x⁻¹ := by
  dsimp only
  apply (MulAut.conj σ).injective
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  apply m.b_inverts
  rw [← hσ]
  exact mem_map_of_mem _ hx

end MarkingConjugacy

/-- Every source marking admits simultaneous direct conjugacy from the standard
nine-group and the ordered transpositions `(standardZ, standardU)`. -/
theorem nonempty_permutationAlignment (m : Marking) : Nonempty (PermutationAlignment m) := by
  obtain ⟨σ, hσ⟩ := MarkingConjugacy.subgroup_conjugacy m.D m.card_D
  let e := MulAut.conj σ
  have hs : ∀ x : Equiv.Perm (Fin 6), x.IsSwap → (e.symm x).IsSwap := by
    intro x hx
    simpa only [e, MulAut.conj_apply, MulAut.conj_symm_apply, inv_inv] using
      MarkingConjugacy.swap_conj σ⁻¹ x hx
  obtain ⟨τ, hτ, hz, hu⟩ := MarkingConjugacy.standard_pair_conjugacy
    (e.symm m.z) (e.symm m.u) (hs m.z m.z_swap) (hs m.u m.u_swap)
    (MarkingConjugacy.pullback_inverts m σ hσ)
  refine ⟨⟨σ * τ, ?_, ?_, ?_⟩⟩
  · have hc : (MulAut.conj (σ * τ)).toMonoidHom =
        (MulAut.conj σ).toMonoidHom.comp (MulAut.conj τ).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, MulAut.mul_apply]
    rw [hc, ← Subgroup.map_map, hτ, hσ]
  · calc
      (σ * τ) * standardZ * (σ * τ)⁻¹ = e (τ * standardZ * τ⁻¹) := by
        simp only [e, MulAut.conj_apply, mul_inv_rev, mul_assoc]
      _ = m.z := by rw [hz, e.apply_symm_apply]
  · calc
      (σ * τ) * standardU * (σ * τ)⁻¹ = e (τ * standardU * τ⁻¹) := by
        simp only [e, MulAut.conj_apply, mul_inv_rev, mul_assoc]
      _ = m.u := by rw [hu, e.apply_symm_apply]

end AlternatingSix.M10.LocalGeometry
