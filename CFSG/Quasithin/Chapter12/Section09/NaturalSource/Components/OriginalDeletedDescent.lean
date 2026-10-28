module

public import Theory.Representation.BinaryPermutation.EightCommutant
public import Theory.Representation.Quotient

/-!
# Descent through the actual hatted-action kernel

A normal subgroup surjects onto the actual quotient actor and acts as the
deleted A₈ module in fixed coordinates. An element of the quotient kernel
commutes with that whole action. Its invertible commutant is trivial, so the
entire representation descends through the same quotient map. No assertion
that the original kernel is a two-group is needed.
Source application: Aschbacher--Smith 12.9.4, printed p.860.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
variable {H J W : Type*} [Group H] [Group J]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The full representation descends through the specified quotient when a
normal surjective component supplies its marked deleted A₈ action. -/
theorem exists_deleted_eight_action_descent
    (K : Subgroup H) [K.Normal] (q : H →* J)
    (hqK : Function.Surjective (q.comp K.subtype))
    (ρ : Representation (ZMod 2) H W)
    (e : J ≃* alternatingGroup (Fin 8))
    (E : W ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hE : ∀ (k : K) w, E (ρ k w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e (q k)) (E w)) :
    ∃ σ : Representation (ZMod 2) J W,
      (∀ h : H, σ (q h) = ρ h) ∧
      ∀ j w, E (σ j w) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e j) (E w) := by
  have hk : q.ker ≤ ρ.ker := by
    intro h hh
    have hqh : q h = 1 := hh
    let F := E.symm.trans ((LinearEquiv.ofBijective (ρ h) (ρ.apply_bijective h)).trans E)
    have hF : F = LinearEquiv.refl _ _ := by
      apply BinaryPermutation.EightCommutant.commuting_eq_refl
      intro a x
      obtain ⟨j, rfl⟩ := e.surjective a
      obtain ⟨k, rfl⟩ := hqK j
      obtain ⟨w, rfl⟩ := E.surjective x
      let k' : K := MulAut.conjNormal h k
      have hqk : q k' = q k := by
        change q (h * (k : H) * h⁻¹) = q k
        simp only [map_mul, map_inv, hqh, one_mul, inv_one, mul_one]
      have he := hE k' (ρ h w)
      rw [hqk] at he
      have hc : ρ h (ρ k w) = ρ k' (ρ h w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        change ρ (h * (k : H)) w = ρ ((h * (k : H) * h⁻¹) * h) w
        rw [mul_assoc, inv_mul_cancel, mul_one]
      change F (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)
        (e (q k)) (E w)) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e (q k)) (F (E w))
      rw [← hE k w]
      change E (ρ h (E.symm (E (ρ k w)))) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e (q k))
          (E (ρ h (E.symm (E w))))
      rw [E.symm_apply_apply, E.symm_apply_apply, hc]
      exact he
    apply LinearMap.ext
    intro w
    have he := congrArg (fun f : BinaryPermutation.natural (Fin 8) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin 8) => f (E w)) hF
    change E (ρ h (E.symm (E w))) = E w at he
    rw [E.symm_apply_apply] at he
    exact E.injective he
  have hq : Function.Surjective q := fun j => by
    obtain ⟨k, hk⟩ := hqK j
    exact ⟨k, hk⟩
  have hkU : q.ker ≤ ρ.asGroupHom.ker := fun h hh => Units.ext (hk hh)
  let σ : Representation (ZMod 2) J W :=
    (Units.coeHom _).comp (q.liftOfSurjective hq ⟨ρ.asGroupHom, hkU⟩)
  have he (h : H) : σ (q h) = ρ h := by
    change Units.coeHom (Module.End (ZMod 2) W)
      ((q.liftOfSurjective hq ⟨ρ.asGroupHom, hkU⟩) (q h)) = _
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    exact Representation.asGroupHom_apply _ _
  refine ⟨σ, he, ?_⟩
  intro j w
  obtain ⟨k, rfl⟩ := hqK j
  change E (σ (q k) w) = _
  rw [he]
  exact hE k w

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
