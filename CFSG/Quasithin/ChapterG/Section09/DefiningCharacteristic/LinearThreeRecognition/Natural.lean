module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.Models
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.FieldTheory.Finiteness

/-!
# Faithfulness and the central quotient in the natural SL₃ case

The natural and dual-natural binary actions are faithful. Thus a surjective
map from SL₃ through which either action factors has trivial kernel and is
an actual group isomorphism. Restriction of scalars gives binary degree 3n
over a coefficient field of order 2ⁿ. These statements identify the cover
once the action has been recognized; they do not classify irreducibles.

Source: Aschbacher--Smith, G.9.3(8), printed pp.354,356.
-/

public section

open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

theorem naturalBinary_injective : Function.Injective (naturalBinary F) := by
  intro g h he
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.toLinearMap_injective
  exact LinearMap.restrictScalars_injective (ZMod 2) he

theorem dualBinary_injective : Function.Injective (dualBinary F) := by
  intro g h he
  have hh := naturalBinary_injective F he
  apply inv_injective
  apply Subtype.ext
  exact Matrix.transpose_injective (congrArg Subtype.val hh)

/-- Both coordinate actions have binary degree three times the field exponent. -/
theorem naturalBinary_finrank [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Module.finrank (ZMod 2) (Fin 3 → F) = 3 * n := by
  let : FiniteDimensional (ZMod 2) F := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [hF, Nat.card_zmod] at h
  have hn : Module.finrank (ZMod 2) F = n :=
    (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) h).symm
  simp [Module.finrank_pi_fintype, hn]

private theorem injective_of_inflation_equiv
    {k H L V W : Type*} [Field k] [Group H] [Group L]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (π : H →* L) (ρ : Representation k L V) (τ : Representation k H W)
    (e : Representation.Equiv (ρ.comp π) τ) (hτ : Function.Injective τ) : Function.Injective π := by
  intro g h hgh
  apply hτ
  ext w
  obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
  have hg := IntertwiningMap.isIntertwining (ρ.comp π) τ e.toIntertwiningMap g v
  have hh := IntertwiningMap.isIntertwining (ρ.comp π) τ e.toIntertwiningMap h v
  exact hg.symm.trans ((congrArg (fun x => e (ρ x v)) hgh).trans hh)

variable {L V : Type*} [Group L] [AddCommGroup V] [Module (ZMod 2) V]

/-- Recognition as either natural action forces an actual SL₃ isomorphism,
not merely an identification of central quotients. -/
theorem natural_cover_recognition [Finite F]
    (π : SL(3,F) →* L) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) L V) {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (h : Nonempty (Representation.Equiv (ρ.comp π) (naturalBinary F)) ∨
      Nonempty (Representation.Equiv (ρ.comp π) (dualBinary F))) :
    π.ker = ⊥ ∧ Nonempty (L ≃* SL(3,F)) ∧ Module.finrank (ZMod 2) V = 3 * n := by
  have hinj : Function.Injective π := by
    rcases h with h | h
    · obtain ⟨e⟩ := h
      exact injective_of_inflation_equiv π ρ _ e (naturalBinary_injective F)
    · obtain ⟨e⟩ := h
      exact injective_of_inflation_equiv π ρ _ e (dualBinary_injective F)
  refine ⟨π.ker_eq_bot_iff.mpr hinj, ⟨(MulEquiv.ofBijective π ⟨hinj, hπ⟩).symm⟩, ?_⟩
  rcases h with h | h
  all_goals
    obtain ⟨e⟩ := h
    exact e.toLinearEquiv.finrank_eq.trans (naturalBinary_finrank F hF)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
