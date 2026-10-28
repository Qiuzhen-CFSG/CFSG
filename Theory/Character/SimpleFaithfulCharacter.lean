module

public import Theory.Character.Orthogonality
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Faithful models of nonprincipal characters of simple groups

A nonprincipal irreducible character of a finite simple group has a faithful
representation. The kernel is either trivial or the whole group. In the latter
case row orthogonality forces the constant character's degree to be one, making
it principal. This includes degree-one characters and needs no nonlinear-degree
assumption.

Source: the ordinary character kernel argument; cf. Fong (1967), p. 74.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

/-- A nonprincipal irreducible character of a finite simple group admits a
faithful model on a standard finite-dimensional complex vector space. -/
public theorem IsIrreducibleCharacter.exists_faithful_of_ne_one
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hnp : χ ≠ 1) :
    ∃ (m : ℕ) (ρ : Representation ℂ G (Fin m → ℂ)),
      Representation.IsIrreducible ρ ∧ χ = ρ.character ∧ Function.Injective ρ := by
  classical
  obtain ⟨m, ρ, hρ, rfl⟩ := hχ
  refine ⟨m, ρ, hρ, rfl, ρ.ker_eq_bot_iff.mp ?_⟩
  rcases (MonoidHom.normal_ker ρ).eq_bot_or_eq_top with hk | hk
  · exact hk
  have hc (g : G) : ρ.character g = (m : ℂ) := by
    have hg : ρ g = 1 := MonoidHom.mem_ker.mp (hk ▸ Subgroup.mem_top g)
    simp [Representation.character, hg]
  have ho := irreducibleCharacter_self (G := G) ⟨m, ρ, hρ, rfl⟩
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hm : (m : ℂ) * m = 1 := by
    simpa [characterProduct, hc, ← Nat.card_eq_fintype_card, hcard,
      ← mul_assoc] using ho
  have hm' : m * m = 1 := by exact_mod_cast hm
  have hm1 : m = 1 := by nlinarith
  exact (hnp (funext fun g => by simp [hc, hm1])).elim
