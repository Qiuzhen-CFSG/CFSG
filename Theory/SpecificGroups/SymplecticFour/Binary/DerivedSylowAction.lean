module

public import Theory.SpecificGroups.AlternatingSix.SylowPointwiseTwoPower
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# The symmetric-group action on the actual derived binary symplectic group

The explicit polar equivalence Sp₄(2) ≃ S₆ restricts to Sp₄(2)′ ≃ A₆.
Transporting permutation conjugation gives a faithful S₆ action on that
exact derived carrier. Its matrix formula agrees with conjugation by the
corresponding element of the full symplectic group.

Every two-power actor fixing a Sylow subgroup belongs to this action image,
by the marked Sylow calculation for Aut(A₆). This proves the small exception
in Aschbacher–Smith, *The Classification of Quasithin Groups*, Lemma 16.1.6,
printed p.1172, with the carrier and action identifications retained.
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.Binary
open AlternatingSix.ShadowLocal
variable {F : Type*} [Field F] [Finite F]

/-- Permutation conjugation transported through the actual derived polar equivalence. -/
noncomputable def derivedPermutationAction (hF : Nat.card F = 2) :
    Equiv.Perm (Fin 6) →* MulAut (commutator (Sp F)) :=
  (MulAut.congr (derivedEquivAlternatingSix hF).symm).toMonoidHom.comp permutationAction

/-- The full symmetric group acts faithfully on the derived carrier. -/
theorem derivedPermutationAction_injective (hF : Nat.card F = 2) :
    Function.Injective (derivedPermutationAction hF) :=
  (MulAut.congr (derivedEquivAlternatingSix hF).symm).injective.comp
    permutationAction_injective

/-- The action is compatible with the displayed A₆ identification. -/
theorem derivedPermutationAction_apply (hF : Nat.card F = 2)
    (σ : Equiv.Perm (Fin 6)) (x : commutator (Sp F)) :
    (derivedEquivAlternatingSix hF (derivedPermutationAction hF σ x) :
      Equiv.Perm (Fin 6)) =
      σ * (derivedEquivAlternatingSix hF x : Equiv.Perm (Fin 6)) * σ⁻¹ := by
  change ((derivedEquivAlternatingSix hF)
    ((derivedEquivAlternatingSix hF).symm
      (permutationAction σ (derivedEquivAlternatingSix hF x))) : Equiv.Perm (Fin 6)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The same action is conjugation by the corresponding actual symplectic matrix. -/
theorem derivedPermutationAction_matrix (hF : Nat.card F = 2)
    (σ : Equiv.Perm (Fin 6)) (x : commutator (Sp F)) :
    (derivedPermutationAction hF σ x : Sp F) =
      (fieldEquivSp (fieldEquivZModTwo F hF)).symm (symmetricSixEquiv σ) *
        (x : Sp F) *
      ((fieldEquivSp (fieldEquivZModTwo F hF)).symm (symmetricSixEquiv σ))⁻¹ := by
  let f := (fieldEquivSp (fieldEquivZModTwo F hF)).trans symmetricSixEquiv.symm
  apply f.injective
  have h := derivedPermutationAction_apply hF σ x
  rw [derivedEquivAlternatingSix_coe, derivedEquivAlternatingSix_coe] at h
  change f (derivedPermutationAction hF σ x : Sp F) = σ * f x * σ⁻¹ at h
  rw [map_mul, map_mul, map_inv]
  have hs : f ((fieldEquivSp (fieldEquivZModTwo F hF)).symm
      (symmetricSixEquiv σ)) = σ := by
    dsimp [f]
    simp only [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  rw [hs]
  exact h

/-- The precise S₆ alternative for arbitrary two-power actors, including order greater than two. -/
theorem derived_twoPower_fixes_sylow (hF : Nat.card F = 2)
    (P : Sylow 2 (commutator (Sp F))) (β : MulAut (commutator (Sp F)))
    {k : ℕ} (hβ : β ^ (2 ^ k) = 1)
    (hfix : ∀ x ∈ (P : Subgroup (commutator (Sp F))), β x = x) :
    ∃ σ : Equiv.Perm (Fin 6), derivedPermutationAction hF σ = β := by
  let e := derivedEquivAlternatingSix hF
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hb : (MulAut.congr e β) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hβ, map_one]
  have hq : ∀ x ∈ (Q : Subgroup A6), MulAut.congr e β x = x := by
    rintro _ ⟨x, hx, rfl⟩
    change e (β (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hfix x hx]
  obtain ⟨σ, hσ⟩ := twoPower_mem_natural_of_fixes_sylow Q _ hb hq
  refine ⟨σ, ?_⟩
  apply (MulAut.congr e).injective
  rw [← hσ]
  apply MulEquiv.ext
  intro x
  change e (e.symm (permutationAction σ (e (e.symm x)))) = permutationAction σ x
  simp only [e.apply_symm_apply]

end Theory.SpecificGroups.SymplecticFour.Binary
