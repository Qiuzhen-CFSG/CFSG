module
public import Theory.Representation.BinaryAlternatingFiveExtension.PlaneAutomorphism
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ExtendedAffinePlane

/-!
# Innerness for the literal doubled unitary plane

Transport the proved innerness of automorphisms of the binary affine group
through the marked equivalence with the literal extended unitary plane.
This lets an ambient comparison that preserves the plane range be adjusted
by an element of that plane to agree on every plane element.

Source: Aschbacher--Smith F.5.7(1), printed p.303. In particular the graph
element, plane core and corrected independent symmetric-four complement
are preserved once the plane embedding has been aligned pointwise.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.ExtendedAffinePlane
open GreenBook.LieModels.UnitaryFour
local notation "PE" => Extension.plane 1 (Nat.le_refl 1)

/-- Every automorphism of the literal doubled binary unitary plane is inner. -/
theorem exists_conj (α : MulAut PE) : ∃ g : PE, α = MulAut.conj g := by
  obtain ⟨e, _, _, _⟩ := exists_marked_plane_equiv
  let β := e.trans (α.trans e.symm)
  obtain ⟨g, hg⟩ := BinaryPermutation.AlternatingFiveExtension.PlaneAutomorphism.exists_conj β
  refine ⟨e g, ?_⟩
  apply MulEquiv.ext
  intro x
  have hh := congrArg (fun a => e (a (e.symm x))) hg
  simpa only [β, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    MulAut.conj_apply, map_mul, map_inv] using hh

end CFSG.Quasithin.ChapterF.UnitaryTwo.ExtendedAffinePlane
