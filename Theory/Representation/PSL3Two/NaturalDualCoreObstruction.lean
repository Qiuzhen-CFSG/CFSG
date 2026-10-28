module

public import Theory.Representation.PSL3Two.FanoCoreStructure

/-!
# The split natural-plus-dual module is not a Fano permutation core

Every map from the binary point core to the dual natural module vanishes.
Projection onto the dual summand therefore excludes an equivalence with
the split natural-plus-dual module. The line core has the dual obstruction.
The two extension lemmas retain the actual permutation homomorphism and
its marking on SL₃(2), so they can be used for an overgroup action.

These are the module obstruction needed for a replacement of the disputed
orbit computation at the end of Aschbacher–Smith 12.7.7, printed p.842
of the combined manuscript (1 March 2004). They do not classify orthogonal
overgroups or construct a seven-point marking for an arbitrary A₇.
-/

public section
open Representation BinaryLinearThree
open BinaryLinearThree.FanoDecomposition
namespace BinaryLinearThree.NaturalDualCoreObstruction

/-- The point augmentation core is not the split six-dimensional module. -/
theorem pointCore_not_equiv_naturalDual : ¬ Nonempty (U₂.Equiv (W.prod W.dual)) := by
  rintro ⟨e⟩
  let f : U₂.IntertwiningMap W.dual :=
    (IntertwiningMap.snd (ZMod 2) W W.dual).comp e.toIntertwiningMap
  apply SimpleHeadQuotientObstruction.core_to_dual_not_surjective f
  intro v
  obtain ⟨x, hx⟩ := e.toLinearEquiv.surjective (0, v)
  exact ⟨x, congrArg Prod.snd hx⟩

/-- The line augmentation core is not the split six-dimensional module. -/
theorem lineCore_not_equiv_naturalDual :
    ¬ Nonempty (lineCoreRepresentation.Equiv (W.prod W.dual)) := by
  rintro ⟨e⟩
  let f : lineCoreRepresentation.IntertwiningMap W :=
    (IntertwiningMap.fst (ZMod 2) W W.dual).comp e.toIntertwiningMap
  obtain ⟨x, hx⟩ := e.toLinearEquiv.surjective (Pi.single 0 1, 0)
  have he := congrArg (fun v : Vector => v 0) (congrArg Prod.fst hx)
  have hf := FanoCoreStructure.lineCore_to_natural_eq_zero f
  have hzero : f x = 0 := congrArg (fun a : lineCoreRepresentation.IntertwiningMap W => a x) hf
  change (f x) 0 = 1 at he
  rw [hzero] at he
  exact zero_ne_one he

/-- A marked seven-point overgroup module cannot restrict to the split
natural-plus-dual representation. Construction of the marking and of the
overgroup's actual core model remains a separate mathematical obligation. -/
theorem no_marked_point_core_extension
    {H M : Type*} [_root_.Group H] [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) H M) (i : BinaryLinearThree.Group →* H)
    (j : H →* Equiv.Perm Point)
    (hmark : ∀ g, j (i g) = pointPerm g)
    (ecore : ρ.Equiv ((BinaryPermutation.coreRepresentation Point).comp j))
    (esplit : Representation.Equiv (ρ.comp i) (W.prod W.dual)) : False := by
  let e : Representation.Equiv (ρ.comp i) U₂ := {
    toLinearEquiv := ecore.toLinearEquiv
    isIntertwining' g := by
      simpa only [U₂, MonoidHom.comp_apply, hmark g] using ecore.isIntertwining' (i g) }
  exact pointCore_not_equiv_naturalDual ⟨e.symm.trans esplit⟩

/-- The other Fano marking gives the same obstruction. -/
theorem no_marked_line_core_extension
    {H M : Type*} [_root_.Group H] [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) H M) (i : BinaryLinearThree.Group →* H)
    (j : H →* Equiv.Perm Line)
    (hmark : ∀ g, j (i g) = linePerm g)
    (ecore : ρ.Equiv ((BinaryPermutation.coreRepresentation Line).comp j))
    (esplit : Representation.Equiv (ρ.comp i) (W.prod W.dual)) : False := by
  let e : Representation.Equiv (ρ.comp i) lineCoreRepresentation := {
    toLinearEquiv := ecore.toLinearEquiv
    isIntertwining' g := by
      simpa only [lineCoreRepresentation, MonoidHom.comp_apply, hmark g]
        using ecore.isIntertwining' (i g) }
  exact lineCore_not_equiv_naturalDual ⟨e.symm.trans esplit⟩

end BinaryLinearThree.NaturalDualCoreObstruction
