module
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Faithfulness of irreducible representations of simple groups

An irreducible complex representation of dimension greater than one of a
finite simple group is faithful. Its kernel is normal; if it were the whole
group, character orthogonality would force the square of the dimension to be
one. This supplies the faithfulness step in the usual rational-character
argument for simple groups (Wong, 1964, Appendix (b)).
-/

open scoped BigOperators
noncomputable section

public theorem Representation.injective_of_isSimpleGroup_of_one_lt_finrank
    {G V : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (hdim : 1 < Module.finrank ℂ V) : Function.Injective ρ := by
  classical
  let := Fintype.ofFinite G
  apply ρ.ker_eq_bot_iff.mp
  rcases (MonoidHom.normal_ker ρ).eq_bot_or_eq_top with h | h
  · exact h
  have hρ : ∀ g, ρ g = 1 := by
    intro g
    exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g)
  have hc : ∀ g, ρ.character g = (Module.finrank ℂ V : ℂ) := by
    intro g
    simp [Representation.character, hρ]
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := G)).ne')
  have ho := Representation.char_orthonormal (ρ := ρ) (σ := ρ)
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  rw [if_pos (show Nonempty (ρ.Equiv ρ) from ⟨Representation.Equiv.refl ρ⟩)] at ho
  simp only [hc,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul] at ho
  have hn : Module.finrank ℂ V * Module.finrank ℂ V = 1 := by exact_mod_cast ho
  nlinarith only [hn, hdim]
