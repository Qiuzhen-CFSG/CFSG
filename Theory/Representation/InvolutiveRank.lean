module
public import Theory.Representation.InvolutiveWeights
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Involutive rank with a fixed vector

A faithful elementary abelian two-group over a field of characteristic different
from two is detected by its nontrivial simultaneous characters. There are at
most as many occurring characters as dimensions. A nonzero fixed vector forces
the trivial character to occur, removing one coordinate from the faithful sign
encoding. This gives the rank bound needed for the odd-field octonion models
in Aschbacher–Smith 4.4.3, printed p.622.
-/

public section
open Module Representation
open scoped IsMulCommutative

namespace Representation
variable {F A V : Type*} [Field F] [Group A] [Finite A]
  [IsElementaryAbelian 2 A] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- A nonzero fixed vector saves one sign coordinate in a faithful involutive action. -/
theorem elementary_card_le_pow_finrank_sub_one_of_fixed
    (ρ : Representation F A V) (hρ : Function.Injective ρ) (h2 : (2 : F) ≠ 0)
    (v : V) (hv : v ≠ 0) (hfix : ∀ a, ρ a v = v) :
    Nat.card A ≤ 2 ^ (Module.finrank F V - 1) := by
  classical
  have hpow (a : A) : a ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have horder : (Nat.card A : F) ≠ 0 := by
    rw [hk, Nat.cast_pow]
    exact pow_ne_zero _ h2
  obtain ⟨hfinite, hdim⟩ := ρ.characterWeight_card_le horder
  let : Finite ρ.CharacterWeight := hfinite
  let := Fintype.ofFinite ρ.CharacterWeight
  have htriv : ρ.characterWeightSpace 1 ≠ ⊥ := by
    intro hbot
    have hmem : v ∈ ρ.characterWeightSpace 1 := by
      simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
      intro a
      simpa using hfix a
    rw [hbot, Submodule.mem_bot] at hmem
    exact hv hmem
  let χ₀ : ρ.CharacterWeight := ⟨1, htriv⟩
  let W := {χ : ρ.CharacterWeight // χ ≠ χ₀}
  have hW : Nat.card W ≤ Module.finrank F V - 1 := by
    have hlt : Fintype.card W < Fintype.card ρ.CharacterWeight :=
      Fintype.card_subtype_lt (x := χ₀) (not_not_intro rfl)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hlt
    omega
  let f : A → (W → rootsOfUnity 2 F) := fun a χ =>
    ⟨χ.val.val a, by rw [mem_rootsOfUnity, ← map_pow, hpow, map_one]⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply ρ.eq_of_characterWeight_values_of_involutive hρ hpow h2 a b
    intro χ
    by_cases hχ : χ = χ₀
    · subst χ; simp [χ₀]
    · exact congrArg Subtype.val (congrFun hab ⟨χ, hχ⟩)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun] at hcard
  exact hcard.trans ((Nat.pow_le_pow_left (card_rootsOfUnity F 2) _).trans
    (Nat.pow_le_pow_right (by decide) hW))
end Representation
