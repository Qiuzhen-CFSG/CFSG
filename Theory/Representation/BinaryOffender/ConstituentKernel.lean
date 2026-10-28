module
public import Theory.Representation.BinaryOffender.FaithfulInvariantSection
public import Theory.Representation.BinaryOffender.Homogeneous.Core

/-!
# The elementary actor kernel on a faithful constituent

An element fixing a faithful section of a normal subgroup centralizes that
subgroup. Conversely, a two-group stabilizing an Irr-plus constituent and
centralizing its group acts trivially on it, since the constituent's linear
centralizer has odd order. These two facts identify the kernel of the literal
restricted representation with the centralizer inside the original actor.

The original natural-flag application is in Chapter12's
`NaturalSource.Components.NonabelianConstituents`. This is the equality
C_X(I) = C_X(H) preceding Aschbacher--Smith G.11.8, printed p.368.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The elementary actor's kernel on a faithful invariant constituent is its
centralizer of the original normal group. -/
theorem constituent_kernel_eq_centralizer
    (ρ : Representation (ZMod 2) D V) (H X : Subgroup D)
    [H.Normal] [IsElementaryAbelian 2 X]
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ H I)
    (hX : X ≤ subspaceStabilizer ρ I)
    (hf : Function.Injective (invariantSubspace ρ H I hI.choose).toRepresentation) :
    (invariantSubspace ρ X I hX).toRepresentation.ker =
      (centralizer (H : Set D)).subgroupOf X := by
  have hC : IsPGroup 2 (X ⊓ centralizer (H : Set D) : Subgroup D) :=
    (IsElementaryAbelian.isPGroup 2 X).to_le inf_le_left
  have hfix := Homogeneous.IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes ρ hI hC
    (show X ⊓ centralizer (H : Set D) ≤ centralizer (H : Set D) from inf_le_right)
    (inf_le_left.trans hX)
  ext x
  constructor
  · intro hx
    refine centralizes_of_fixes_faithful_section ρ H I hI.choose ?_
      (le_normalizer_of_normal (mem_top (x : D))) ?_
    · intro a ha hfa
      have he : (⟨a,ha⟩ : H) = 1 := hf (by
        rw [map_one]
        apply LinearMap.ext
        intro w
        exact Subtype.ext (hfa w w.property))
      exact congrArg Subtype.val he
    · intro w hw
      exact congrArg (fun f : Module.End (ZMod 2) I => (f ⟨w,hw⟩ : V)) hx
  · intro hx
    apply LinearMap.ext
    intro w
    exact Subtype.ext (hfix w.property ⟨x,⟨x.property,hx⟩⟩)
end Representation.BinaryOffender
