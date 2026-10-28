module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import Theory.Representation.NormalComponentConstituents

/-!
# Whole natural coordinates from an irreducible moved section

A nontrivial normal subgroup of a faithful irreducible action moves the whole
module and has zero fixed space. Thus the original moved central quotient has
a zero central kernel and supplies injective natural coordinates on the whole
module. The theorem retains the actual subgroup inclusion and its action.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, proof of 3.1.9(5), printed p.578.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite D] in
theorem whole_natural_coordinate_of_moved_section
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ) (hi : IsIrreducible ρ)
    (Y : Subgroup D) (A : Subgroup Y) [(A.map Y.subtype).Normal] (hne : A ≠ ⊥)
    (s : MovedSection (ρ.comp Y.subtype) A)
    (F : BinaryField) (e : ActionEquiv (s.action.comp A.subtype) (linearNatural F 2)) :
    ∃ f : W →ₗ[ZMod 2] (Fin 2 → F.Carrier), Function.Injective f ∧
      ∀ (a : A) w, f (ρ ((a : Y) : D) w) = linearNatural F 2 (e.groupEquiv a) (f w) := by
  have hLne : A.map Y.subtype ≠ ⊥ := fun he =>
    hne ((map_eq_bot_iff_of_injective A Y.subtype_injective).mp he)
  have hfixed := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hfaith hi _ hLne
  have hspace : s.space.toSubmodule = ⊤ := by
    rw [s.space_eq,moved_comp_map]
    exact subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hfaith hi _ hLne
  let z : W →ₗ[ZMod 2] s.space.toSubmodule := {
    toFun w := ⟨w,hspace ▸ Submodule.mem_top⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let f := e.linearEquiv.toLinearMap.comp (s.central.toSubmodule.mkQ.comp z)
  have hcentral : s.central.toSubmodule = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro w hw
    rw [s.central_eq] at hw
    have hw' : (w : W) ∈ fixedSpace ρ (A.map Y.subtype) := by
      rw [←fixedSpace_comp_map]
      intro a
      exact congrArg Subtype.val (hw a)
    rw [hfixed,Submodule.mem_bot] at hw'
    exact Subtype.ext hw'
  refine ⟨f,?_,?_⟩
  · intro a b hab
    have he : s.central.toSubmodule.mkQ (z a) = s.central.toSubmodule.mkQ (z b) :=
      e.linearEquiv.injective hab
    have hm := (Submodule.Quotient.eq s.central.toSubmodule).mp he
    rw [hcentral,Submodule.mem_bot,sub_eq_zero] at hm
    exact congrArg Subtype.val hm
  · intro a w
    exact e.intertwines a (s.central.toSubmodule.mkQ (z w))
end CFSG.Quasithin.ChapterB.QuasisimpleSource
