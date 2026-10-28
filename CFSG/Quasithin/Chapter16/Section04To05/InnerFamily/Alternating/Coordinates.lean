module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.ZMod.Basic

/-!
# Marked permutation coordinates for the alternating branches

The common construction target is an isomorphism of the actual subgroup
LE = L⟨r,z⟩ with Sₙ × C₂, respecting L, z and the cycle type of r. Projecting
this isomorphism gives a surjective permutation action whose kernel is
exactly ⟨z⟩. The proof of the kernel assertion uses the two elements of C₂.

The existence of the product identification is a separate obligation. In
particular, this interface does not identify LT with LE: the full Aut(A₆)
overgroup is allowed, and both A₈ outer cycle types are retained. There are
no assumptions about fusion or a five-point normalizer action in this record.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections
variable {G : Type*} [Group G]

/-- The actual subgroup LE = L⟨r,z⟩, kept separate from the possibly larger LT. -/
abbrev AlternatingOvergroup (L : Subgroup G) (z r : G) : Subgroup G :=
  (L ⊔ zpowers r) ⊔ zpowers z

/-- A marked identification of the actual ambient subgroup LE with Sₙ × C₂.
This is a construction target; no existence is asserted here. The component,
central involution and outer involution are all retained by the identification.
For A₆ the coordinate choice uses a transposition; for A₈ both outer cycle
types are allowed. The record makes no assertion that LT = LE. -/
structure AlternatingProductModel (L : Subgroup G) (z r : G) (n : ℕ) where
  equiv : AlternatingOvergroup L z r ≃* (Equiv.Perm (Fin n) × Multiplicative (ZMod 2))
  component_iff : ∀ a : AlternatingOvergroup L z r,
    (a : G) ∈ L ↔ (equiv a).1 ∈ alternatingGroup (Fin n) ∧ (equiv a).2 = 1
  central_image : equiv ⟨z, mem_sup_right (mem_zpowers z)⟩ = (1, Multiplicative.ofAdd 1)
  outer_second : (equiv ⟨r, mem_sup_left (mem_sup_right (mem_zpowers r))⟩).2 = 1
  outer_cycleType :
    (equiv ⟨r, mem_sup_left (mem_sup_right (mem_zpowers r))⟩).1.cycleType = {2} ∨
      n = 8 ∧ (equiv ⟨r, mem_sup_left (mem_sup_right (mem_zpowers r))⟩).1.cycleType = {2, 2, 2}

namespace AlternatingProductModel
variable {L : Subgroup G} {z r : G} {n : ℕ}

/-- Projection through the actual product identification gives the source action on n points. -/
def permutationAction (M : AlternatingProductModel L z r n) :
    AlternatingOvergroup L z r →* Equiv.Perm (Fin n) :=
  (MonoidHom.fst _ _).comp M.equiv.toMonoidHom

/-- The permutation image is the whole symmetric group. -/
theorem permutationAction_surjective (M : AlternatingProductModel L z r n) :
    Function.Surjective M.permutationAction := by
  intro p
  refine ⟨M.equiv.symm (p, 1), ?_⟩
  change (M.equiv (M.equiv.symm (p, 1))).1 = p
  rw [M.equiv.apply_symm_apply]

/-- The action kernel inside LE is precisely its marked central factor. -/
theorem permutationAction_kernel (M : AlternatingProductModel L z r n) :
    M.permutationAction.ker = zpowers (⟨z, mem_sup_right (mem_zpowers z)⟩ : AlternatingOvergroup L z r) := by
  apply le_antisymm
  · intro a ha
    have ha1 : (M.equiv a).1 = 1 := ha
    have hcases : (M.equiv a).2 = 1 ∨ (M.equiv a).2 = Multiplicative.ofAdd 1 := by
      generalize (M.equiv a).2 = c
      change ZMod 2 at c
      change c = (0 : ZMod 2) ∨ c = (1 : ZMod 2)
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hcases with hc | hc
    · have he : a = 1 := M.equiv.injective (by
        rw [map_one]
        exact Prod.ext ha1 hc)
      rw [he]
      exact one_mem _
    · have he : a = ⟨z, mem_sup_right (mem_zpowers z)⟩ := M.equiv.injective (by
        rw [M.central_image]
        exact Prod.ext ha1 hc)
      rw [he]
      exact mem_zpowers _
  · apply zpowers_le.mpr
    change (M.equiv ⟨z, mem_sup_right (mem_zpowers z)⟩).1 = 1
    rw [M.central_image]

/-- In the ambient group the action kernel is exactly ⟨z⟩. -/
theorem permutationAction_kernel_image (M : AlternatingProductModel L z r n) :
    M.permutationAction.ker.map (AlternatingOvergroup L z r).subtype = zpowers z := by
  rw [M.permutationAction_kernel, MonoidHom.map_zpowers]
  rfl

end AlternatingProductModel
end CFSG.Quasithin.Chapter16.Intersections
