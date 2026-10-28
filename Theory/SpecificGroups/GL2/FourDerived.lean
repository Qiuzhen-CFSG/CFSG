module
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The literal derived subgroup of GL₂(4)

The determinant kernel is the special linear image. Since SL₂(4) is A₅
and is perfect, this image is exactly the full derived subgroup. The
result retains the original matrix inclusion for plane-overlap markings.
-/

public noncomputable section
open Subgroup Matrix
open scoped commutatorElement
namespace Representation.SL2FourNatural.SemilinearNormalizer

/-- The actual derived subgroup is the literal determinant-one matrix image. -/
theorem linear_commutator_eq_special_range :
    _root_.commutator LinearGroup =
      (SpecialLinearGroup.toGL : SL →* LinearGroup).range := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect SL := Group.IsPerfect.ofSurjective
    (f := alternatingFiveEquiv.symm.toMonoidHom) alternatingFiveEquiv.symm.surjective
  let f : SL →* LinearGroup := SpecialLinearGroup.toGL
  have hker : (GeneralLinearGroup.det : LinearGroup →* Fˣ).ker = f.range := by
    ext g
    constructor
    · intro hg
      have hd : g.val.det = 1 := congrArg Units.val hg
      refine ⟨⟨g.val,hd⟩,?_⟩
      apply Units.ext
      rfl
    · rintro ⟨g,rfl⟩
      exact Units.ext g.property
  apply le_antisymm
  · rw [← hker]
    exact Abelianization.commutator_subset_ker _
  · have hh := map_commutator_eq SL f
    rw [Group.IsPerfect.commutator_eq_top,← MonoidHom.range_eq_map] at hh
    exact hh.trans_le (commutator_mono le_top le_top)

/-- Recognition of that same matrix-derived subgroup as A₅. -/
theorem linear_commutator_equiv_alternatingFive :
    Nonempty (_root_.commutator LinearGroup ≃* alternatingGroup (Fin 5)) :=
  ⟨((MulEquiv.subgroupCongr linear_commutator_eq_special_range).trans
    (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).symm).trans
      alternatingFiveEquiv⟩

end Representation.SL2FourNatural.SemilinearNormalizer
