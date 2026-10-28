module

public import Theory.Representation.CyclicDefect.ProjectivePairing.Characters
public import Theory.Representation.CyclicDefect.ProjectivePairing.Projectivity
public import Theory.Representation.CyclicDefect.ProjectivePairing.LiftContracts

/-!
# Projective tensor pairings from ordinary lifts

The character of `linHom P (ρ ⊗ σ)` is the product of the two Brauer characters
and the conjugate of the projective character. Given an ordinary model agreeing
on regular elements and vanishing on singular elements, its full character
average is exactly the requested regular pairing. Ordinary character averaging
identifies this with a natural dimension.

This is the averaging step of Feit IV.3.3 (printed pp.145–146). The construction
of the ordinary model remains an explicit prerequisite: neither the conditional
theorems here nor the lifting contracts establish projective lifting.
-/

public section
noncomputable section
open scoped BigOperators

namespace Representation.CyclicDefect

variable {K G V W U : Type*} [Field K] [IsAlgClosed K] [Group G] [Finite G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  {m : ℕ} (p : ℕ) (L : CyclicRootLift K m)

/-- Feit's averaging step, given the actual ordinary model of the projective
linear-Hom representation. Constructing that model is a separate obligation. -/
theorem regularPairing_tensor_eq_finrank_of_ordinaryModel
    (horder : ∀ g : G, ¬ p ∣ orderOf g → orderOf g ∣ m)
    (ρ : Representation K G V) (σ : Representation K G W) (P : Representation K G U)
    (M : ProjectivePairing.OrdinaryModel p L (linHom P (ρ.tprod σ))) :
    regularPairing p (fun g => L.value ρ g * L.value σ g) (L.value P) =
      (Module.finrank ℂ M.rep.invariants : ℂ) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne')
  calc
    regularPairing p (fun g => L.value ρ g * L.value σ g) (L.value P) =
        (Nat.card G : ℂ)⁻¹ * ∑ g : G, M.rep.character g := by
      unfold regularPairing
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : ¬ p ∣ orderOf g
      · rw [if_pos hg]
        have hgm : g ^ m = 1 := (orderOf_dvd_iff_pow_eq_one).mp (horder g hg)
        rw [M.regular_eq g hg, L.value_linHom P (ρ.tprod σ) g hgm,
          L.value_tensor ρ σ g hgm]
        ring
      · rw [if_neg hg, M.singular_zero g (not_not.mp hg)]
    _ = (Module.finrank ℂ M.rep.invariants : ℂ) := M.rep.card_inv_mul_sum_char_eq_finrank

/-- Nonnegative integrality after the ordinary projective comparison is supplied. -/
theorem regularPairing_tensor_nat_of_ordinaryModel
    (horder : ∀ g : G, ¬ p ∣ orderOf g → orderOf g ∣ m)
    (ρ : Representation K G V) (σ : Representation K G W) (P : Representation K G U)
    (M : ProjectivePairing.OrdinaryModel p L (linHom P (ρ.tprod σ))) :
    ∃ n : ℕ, regularPairing p (fun g => L.value ρ g * L.value σ g) (L.value P) = (n : ℂ) :=
  ⟨_, regularPairing_tensor_eq_finrank_of_ordinaryModel p L horder ρ σ P M⟩

end Representation.CyclicDefect
