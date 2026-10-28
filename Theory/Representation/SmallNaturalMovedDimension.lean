module

public import Theory.Representation.BinaryOffender.ConjugateMovedDimension
public import Theory.Representation.SLThreeCentralExtension.Involutions
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Moved dimensions for the small transvection factors

An arbitrary binary representation of SL₃(2) has moved dimension at most
three times the displacement rank of any involution. For Sₙ₊₁ the analogous
bound is n for a transposition, because the adjacent transpositions generate.
The S₃ specialization applies to every involution. No semisimplicity or
vanishing fixed space is assumed. These bounds recover natural moved modules
from their actual central quotients in G.6.4.

Source: Aschbacher–Smith, G.6.4, printed pp.345–346, and B.4.8(2), p.91.
-/

public section
open Subgroup Representation.BinaryOffender
namespace Representation.SmallNaturalMovedDimension
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The SL₃ bound applies to the original action, before removing any fixed kernel. -/
theorem linearThree (ρ : Representation (ZMod 2) G V)
    (e : G ≃* BinaryLinearThree.Group) (t : G) (hne : t ≠ 1) (ht : t * t = 1) :
    Module.finrank (ZMod 2) (Coinvariants.ker ρ) ≤
      3 * Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) := by
  obtain ⟨g, hg⟩ := BinaryLinearThree.NaturalExtension.exists_three_conjugate_generators
    (e t) (fun hh => hne (e.injective (hh.trans e.map_one.symm)))
    (by simp only [← map_mul, ht, map_one])
  exact finrank_coinvariants_le_mul_displacement_of_equiv_conjugate_generation ρ e t g hg

/-- Adjacent transpositions give a bound for every degree, on the whole moved space. -/
theorem symmetric (ρ : Representation (ZMod 2) G V) {n : ℕ}
    (e : G ≃* Equiv.Perm (Fin (n + 1))) (t : G) (ht : (e t).IsSwap) :
    Module.finrank (ZMod 2) (Coinvariants.ker ρ) ≤
      n * Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) := by
  obtain ⟨x, y, hxy, he⟩ := ht
  have hc (i : Fin n) : ∃ c : Equiv.Perm (Fin (n + 1)),
      c * e t * c⁻¹ = Equiv.swap i.castSucc i.succ := by
    rw [he]
    exact isConj_iff.mp (Equiv.Perm.isConj_swap hxy (by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega))
  choose c hc using hc
  apply finrank_coinvariants_le_mul_displacement_of_equiv_conjugate_generation ρ e t c
  simp_rw [hc]
  exact closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n)

/-- Every nonidentity involution in S₃ is a transposition. -/
theorem symmetricThree (ρ : Representation (ZMod 2) G V)
    (e : G ≃* Equiv.Perm (Fin 3)) (t : G) (hne : t ≠ 1) (ht : t * t = 1) :
    Module.finrank (ZMod 2) (Coinvariants.ker ρ) ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) := by
  apply symmetric ρ e t
  have hsmall : ∀ s : Equiv.Perm (Fin 3), s ≠ 1 → s * s = 1 → s.IsSwap := by
    simp only [Equiv.Perm.IsSwap]
    decide
  exact hsmall (e t) (fun hh => hne (e.injective (hh.trans e.map_one.symm)))
    (by simp only [← map_mul, ht, map_one])

end Representation.SmallNaturalMovedDimension
