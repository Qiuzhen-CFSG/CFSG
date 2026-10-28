module
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.Weyl
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# All nonzero parameters in the C₂ Weyl formulas

Independent root-lattice rescaling preserves every chamber relation. The
literal Weyl permutation group has eight elements; their two coefficient
identities verify this without any matrix-word relation. Applying the proved
parameter-one formulas to these rescaled roots gives the complete simple
Weyl conjugation formulas, including both opposite-root pairs.

Source: Steinberg §6, Lemma 37(a), pp.69–70. The proof applies to finite
characteristic-two fields without any lower bound on their size.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.RootPresentation

private def weylEight : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | σ = 1 ∨ σ = shortReflection ∨ σ = longReflection ∨
    σ = shortReflection * longReflection ∨ σ = longReflection * shortReflection ∨
    σ = shortReflection * longReflection * shortReflection ∨
    σ = longReflection * shortReflection * longReflection ∨
    σ = shortReflection * longReflection * shortReflection * longReflection}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro σ τ (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
      decide
  inv_mem' := by
    rintro σ (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> decide

/-- The literal reflection permutations generate exactly the eight C₂ chambers. -/
theorem weyl_cases (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ weyl) :
    σ = 1 ∨ σ = shortReflection ∨ σ = longReflection ∨
    σ = shortReflection * longReflection ∨ σ = longReflection * shortReflection ∨
    σ = shortReflection * longReflection * shortReflection ∨
    σ = longReflection * shortReflection * longReflection ∨
    σ = shortReflection * longReflection * shortReflection * longReflection := by
  have h : weyl ≤ weylEight := by
    apply (closure_le _).mpr
    rintro σ (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  exact h hσ

variable {F E : Type*} [Field F] [Group E]

/-- Root-lattice scaling, with independent parameters for short and long simple roots. -/
def rootScale (a b : Fˣ) : Fin 8 → Fˣ :=
  ![a^2*b, (a^2*b)⁻¹, b, b⁻¹, a*b, (a*b)⁻¹, a, a⁻¹]

private theorem rootScale_crossing (a b : Fˣ) (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ weyl) :
    rootScale a b (σ 0) = rootScale a b (σ 6)^2 * rootScale a b (σ 2) ∧
    rootScale a b (σ 4) = rootScale a b (σ 6) * rootScale a b (σ 2) := by
  rcases weyl_cases σ hσ with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [rootScale, shortReflection, longReflection, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, pow_two, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] <;>
    (repeat' apply And.intro) <;> apply Units.ext <;>
    simp only [Units.val_mul, Units.val_inv_eq_inv_val] <;> field_simp

/-- Independent rescaling of the simple roots preserves every imposed relation. -/
theorem Relations.scale {x : Fin 8 → F → E} (h : Relations x) (a b : Fˣ) :
    Relations (fun r u => x r ((rootScale a b r : F) * u)) := by
  intro σ hσ
  refine {add := ?_, commuting := ?_, crossing := ?_}
  · intro r s t
    simpa only [mul_add] using h.positive.add (σ r)
      ((rootScale a b (σ r) : F) * s) ((rootScale a b (σ r) : F) * t)
  · intro i s t
    exact (h σ hσ).commuting i _ _
  · intro v c
    obtain ⟨h0,h4⟩ := rootScale_crossing a b σ hσ
    have h0' : (rootScale a b (σ 0) : F) =
        (rootScale a b (σ 6) : F)^2 * (rootScale a b (σ 2) : F) := by
      exact_mod_cast h0
    have h4' : (rootScale a b (σ 4) : F) =
        (rootScale a b (σ 6) : F) * (rootScale a b (σ 2) : F) := by
      exact_mod_cast h4
    have e0 : (rootScale a b (σ 0) : F) * (c^2*v) =
        ((rootScale a b (σ 6) : F) * c)^2 * ((rootScale a b (σ 2) : F) * v) := by
      rw [h0']; ring
    have e4 : (rootScale a b (σ 4) : F) * (c*v) =
        ((rootScale a b (σ 6) : F) * c) * ((rootScale a b (σ 2) : F) * v) := by
      rw [h4']; ring
    dsimp only
    rw [e0,e4]
    exact (h σ hσ).crossing _ _

/-- Parameter factors for conjugation by a short-root Weyl word. -/
def shortFactor (t : Fˣ) : Fin 8 → Fˣ :=
  ![(t⁻¹)^2,t^2,t^2,(t⁻¹)^2,1,1,(t⁻¹)^2,t^2]

/-- Parameter factors for conjugation by a long-root Weyl word. -/
def longFactor (t : Fˣ) : Fin 8 → Fˣ :=
  ![1,1,(t⁻¹)^2,t^2,t⁻¹,t,t,t⁻¹]

private theorem shortFactor_eq (t : Fˣ) (r : Fin 8) :
    shortFactor t r = rootScale t 1 (shortReflection r) * (rootScale t 1 r)⁻¹ := by
  fin_cases r <;> simp [shortFactor, rootScale, shortReflection, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, pow_two, mul_assoc]

private theorem longFactor_eq (t : Fˣ) (r : Fin 8) :
    longFactor t r = rootScale 1 t (longReflection r) * (rootScale 1 t r)⁻¹ := by
  fin_cases r <;> simp [longFactor, rootScale, longReflection, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def, pow_two, mul_assoc]

variable [Finite F] [CharP F 2]

/-- Full short-root Weyl conjugation, including its own opposite pair. -/
theorem Relations.shortWord_conj {x : Fin 8 → F → E} (h : Relations x)
    (t : Fˣ) (r : Fin 8) (u : F) :
    shortWord x (t : F) * x r u * (shortWord x (t : F))⁻¹ =
      x (shortReflection r) ((shortFactor t r : F) * u) := by
  have he := (h.scale t 1).shortWord_one_conj r ((rootScale t 1 r : F)⁻¹ * u)
  have hw : shortWord (fun r u => x r ((rootScale t 1 r : F) * u)) 1 =
      shortWord x (t : F) := by simp [shortWord, rootScale]
  rw [hw] at he
  simpa only [shortFactor_eq, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc,
    mul_inv_cancel_left₀ (Units.ne_zero _)] using he

/-- Full long-root Weyl conjugation, including its own opposite pair. -/
theorem Relations.longWord_conj {x : Fin 8 → F → E} (h : Relations x)
    (t : Fˣ) (r : Fin 8) (u : F) :
    longWord x (t : F) * x r u * (longWord x (t : F))⁻¹ =
      x (longReflection r) ((longFactor t r : F) * u) := by
  have he := (h.scale 1 t).longWord_one_conj r ((rootScale 1 t r : F)⁻¹ * u)
  have hw : longWord (fun r u => x r ((rootScale 1 t r : F) * u)) 1 =
      longWord x (t : F) := by simp [longWord, rootScale]
  rw [hw] at he
  simpa only [longFactor_eq, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc,
    mul_inv_cancel_left₀ (Units.ne_zero _)] using he

end Theory.SpecificGroups.SymplecticFour.RootPresentation
