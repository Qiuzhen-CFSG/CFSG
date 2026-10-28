module
public import Theory.Representation.BinaryOffender.CubicRatio
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cubic centralizer actions with a nonfixed final line

A linear map commuting with a group cannot have nonzero image in a binary
line that the group does not fix: a nonzero such image is the entire line,
and every linear automorphism of a binary line is trivial.

Consequently, if the third displacements of an actor lie in that line,
its intersection with the group centralizer acts cubically. This uses no
fixedness assumption on an intermediate subspace. The original opposite
factor in Aschbacher--Smith 5.1.23 is an application (printed p.645).
-/

public noncomputable section
open Subgroup

namespace Representation.BinaryOffender
variable {X M : Type*} [Group X] [AddCommGroup M] [Module (ZMod 2) M]

/-- Equivariance kills a map whose range lies in a nonfixed binary line. -/
theorem equivariant_range_in_nonfixed_binary_line
    (ρ : Representation (ZMod 2) X M) (K : Subgroup X)
    (P : Submodule (ZMod 2) M) (hP : Nat.card P = 2)
    (hn : ¬ P ≤ fixedSpace ρ K)
    (f : M →ₗ[ZMod 2] M) (hf : LinearMap.range f ≤ P)
    (he : ∀ k ∈ K, ∀ v, ρ k (f v) = f (ρ k v)) : f = 0 := by
  classical
  apply LinearMap.ext
  intro v
  change f v = 0
  by_contra hv
  have hfv : f v ∈ P := hf ⟨v,rfl⟩
  obtain ⟨w,hw,hall⟩ := (Nat.card_eq_two_iff' (0 : P)).mp hP
  have unique (a b : P) (ha : a ≠ 0) (hb : b ≠ 0) : a = b :=
    (hall a ha).trans (hall b hb).symm
  have hfix (k : K) : ρ k (f v) = f v := by
    have hm : ρ k (f v) ∈ P := by rw [he k k.property]; exact hf ⟨ρ k v,rfl⟩
    have hz : ρ k (f v) ≠ 0 := by
      intro hh
      have hback := congrArg (ρ (k : X)⁻¹) hh
      rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
        Module.End.one_apply,map_zero] at hback
      exact hv hback
    exact congrArg Subtype.val (unique ⟨ρ k (f v),hm⟩ ⟨f v,hfv⟩
      (fun e => hz (congrArg Subtype.val e)) (fun e => hv (congrArg Subtype.val e)))
  apply hn
  intro u hu k
  by_cases hz : u = 0
  · simp only [hz,map_zero]
  · have hh : u = f v := congrArg Subtype.val
      (unique ⟨u,hu⟩ ⟨f v,hfv⟩ (fun e => hz (congrArg Subtype.val e))
        (fun e => hv (congrArg Subtype.val e)))
    rw [hh]
    exact hfix k

/-- The centralizing part of an actor has zero third displacement. -/
theorem cubic_centralizer_of_third_displacement_line
    (ρ : Representation (ZMod 2) X M) (K E : Subgroup X)
    (P : Submodule (ZMod 2) M) (hP : Nat.card P = 2)
    (hn : ¬ P ≤ fixedSpace ρ K)
    (hline : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ v,
      displacement ρ a (displacement ρ b (displacement ρ c v)) ∈ P) :
    IsCubic ρ (E ⊓ centralizer (K : Set X)) := by
  intro a ha b hb c hc v
  let f := (ρ a - 1).comp ((ρ b - 1).comp (ρ c - 1))
  have commute (a : X) (ha : a ∈ centralizer (K : Set X)) (k : X) (hk : k ∈ K)
      (v : M) : ρ k (displacement ρ a v) = displacement ρ a (ρ k v) := by
    change ρ k (ρ a v - v) = ρ a (ρ k v) - ρ k v
    rw [map_sub,← Module.End.mul_apply,← map_mul,ha k hk,map_mul,Module.End.mul_apply]
  have he : f = 0 := equivariant_range_in_nonfixed_binary_line ρ K P hP hn f
    (by rintro _ ⟨u,rfl⟩; exact hline a ha.1 b hb.1 c hc.1 u)
    (by intro k hk u; change ρ k (displacement ρ a (displacement ρ b (displacement ρ c u))) =
          displacement ρ a (displacement ρ b (displacement ρ c (ρ k u)))
        rw [commute a ha.2 k hk,commute b hb.2 k hk,commute c hc.2 k hk])
  exact LinearMap.congr_fun he v
end Representation.BinaryOffender

