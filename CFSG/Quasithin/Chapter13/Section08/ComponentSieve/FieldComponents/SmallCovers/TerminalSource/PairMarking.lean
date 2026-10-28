module

public import Theory.Representation.BinaryPermutation.SixPairsQuadratic
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The parabolic marking required for the alternative-section argument

`Pairs.Marking` records an actual equivariant identification of parabolic
cosets with the fifteen pairs of six letters and lifts of the two double
transpositions in the intrinsic two-core. The pair-module calculation then
excludes a noncentral quadratic quotient of this coset permutation module.

For Aschbacher–Smith 13.8.21(2), printed p.956, this input must be constructed
from the marked F₄-point stabilizer in the actual six-dimensional cover
module. It is deliberately separate from the source adapter so that the
intrinsic model calculation can import it without an assembly cycle.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource
open Subgroup Representation.BinaryOffender

namespace Pairs
open BinaryPermutation.SixPairsQuadratic

/-- A concrete identification of the parabolic coset action with the fifteen
pairs, including two lifts in its actual two-core. This is geometric input,
not a conclusion of the source contradiction. -/
structure Marking {H : Type*} [Group H] (P : Subgroup H) where
  coordinate : H →* Equiv.Perm (Fin 6)
  coversAlternating : ∀ g : alternatingGroup (Fin 6), ∃ h : H, coordinate h = g.val
  cosets : (H ⧸ P) ≃ Pair
  equivariant : ∀ h ω, cosets (h • ω) = pairPerm (coordinate h) (cosets ω)
  firstLift : H
  secondLift : H
  first_mem : firstLift ∈ P.pCoreIn 2
  second_mem : secondLift ∈ P.pCoreIn 2
  coordinate_first : coordinate firstLift = first
  coordinate_second : coordinate secondLift = second

variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]

/-- Transfer the pair-module calculation through actual equivariant coset
coordinates. The action on the target is the supplied quotient action. -/
theorem noncentral_quotient_not_quadratic (P : Subgroup H) (m : Marking P)
    (ρ : Representation (ZMod 2) H V)
    (f₀ : BinaryPermutation.Full (H ⧸ P) →ₗ[ZMod 2] V)
    (hf₀ : Function.Surjective f₀)
    (heq₀ : ∀ h v, f₀ (BinaryPermutation.representation
      (H ⧸ P) (MulAction.toPerm h) v) = ρ h (f₀ v))
    (hnoncentral : ∃ h v, ρ h v ≠ v) : ¬ IsQuadratic ρ (P.pCoreIn 2) := by
  let c : BinaryPermutation.Full Pair ≃ₗ[ZMod 2] BinaryPermutation.Full (H ⧸ P) :=
    { toFun := fun v => v ∘ m.cosets
      invFun := fun v => v ∘ m.cosets.symm
      left_inv := by intro v; ext i; simp
      right_inv := by intro v; ext i; simp
      map_add' := by intro v w; rfl
      map_smul' := by intro a v; rfl }
  have hc (h : H) (v : BinaryPermutation.Full Pair) :
      c (action (m.coordinate h) v) =
        BinaryPermutation.representation (H ⧸ P) (MulAction.toPerm h) (c v) := by
    ext ω
    change v ((pairPerm (m.coordinate h)).symm (m.cosets ω)) =
      v (m.cosets (h⁻¹ • ω))
    rw [m.equivariant, map_inv]
    rfl
  apply not_quadratic_of_noncentral_quotient m.coordinate m.coversAlternating ρ
    (f₀.comp c.toLinearMap) (hf₀.comp c.surjective) ?_ hnoncentral
    (P.pCoreIn 2) m.firstLift m.secondLift m.first_mem m.second_mem
    m.coordinate_first m.coordinate_second
  intro h v
  change f₀ (c (action (m.coordinate h) v)) = ρ h (f₀ (c v))
  rw [hc, heq₀]

end Pairs

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource
