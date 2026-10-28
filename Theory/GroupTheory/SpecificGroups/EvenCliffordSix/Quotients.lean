module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Basic

/-!
# The two literal binary projections

The sign quotient is the augmentation core. Its subsequent natural-module
projection has precisely the vectors in the constant line as kernel. Both
coordinate maps retain their equations under the direct signed permutation
formula. Identification of this latter kernel with the full center is the
separate central-product calculation.

Source: Aschbacher–Smith I.2.2(6), printed pp.410 and 412, combined manuscript
of 1 March 2004; the natural section is that of B.3, printed p.83.
-/

@[expose] public section
namespace EvenCliffordSix
open BinaryPermutation

/-- The original map to the deleted permutation section. -/
def naturalProjection : Model →* Multiplicative (natural (Fin 6)) where
  toFun x := Multiplicative.ofAdd (coreToNatural (Fin 6) x.vector)
  map_one' := congrArg Multiplicative.ofAdd (map_zero (coreToNatural (Fin 6)))
  map_mul' x y := congrArg Multiplicative.ofAdd (map_add (coreToNatural (Fin 6))
    x.vector y.vector)

@[simp] theorem naturalProjection_apply (x : Model) :
    (naturalProjection x).toAdd = coreToNatural (Fin 6) x.vector := rfl

/-- This uses surjectivity onto the actual image of the core. -/
theorem naturalProjection_surjective : Function.Surjective naturalProjection := by
  intro y
  obtain ⟨u, hu, he⟩ := y.toAdd.property
  refine ⟨⟨0, ⟨u, hu⟩⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  exact Subtype.ext he

/-- Literal description of the second kernel before center recognition. -/
theorem mem_naturalProjection_ker (x : Model) :
    x ∈ naturalProjection.ker ↔ x.vector.val ∈ constants (Fin 6) := by
  change coreToNatural (Fin 6) x.vector = 0 ↔ _
  constructor
  · intro h
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h)

/-- The two natural projections have the prescribed order. -/
theorem signKernel_le_naturalProjection_ker : signKernel ≤ naturalProjection.ker := by
  intro x hx
  change coreToNatural (Fin 6) x.vector = 0
  rw [(mem_signKernel x).mp hx, map_zero]

/-- The quotient retains the specified natural-module projection. -/
noncomputable def naturalQuotientEquiv :
    (Model ⧸ naturalProjection.ker) ≃* Multiplicative (natural (Fin 6)) :=
  QuotientGroup.quotientKerEquivOfSurjective naturalProjection naturalProjection_surjective

@[simp] theorem naturalQuotientEquiv_mk (x : Model) :
    naturalQuotientEquiv (QuotientGroup.mk' naturalProjection.ker x) =
      Multiplicative.ofAdd (coreToNatural (Fin 6) x.vector) := rfl

/-- The signed formula projects to the literal natural permutation action. -/
theorem signedTo_naturalProjection (p : Equiv.Perm (Fin 6)) (x : Model) :
    (naturalProjection (signedTo p x)).toAdd =
      naturalRepresentation (Fin 6) p (naturalProjection x).toAdd := by
  apply Subtype.ext
  rfl

end EvenCliffordSix
