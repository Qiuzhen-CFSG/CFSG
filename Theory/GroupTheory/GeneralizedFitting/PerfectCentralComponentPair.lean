module

public import Theory.GroupTheory.GeneralizedFitting.PerfectCentralSemisimple

/-!
# Marked component pairs through a perfect central cover

Lift the two target components by the canonical component-lifting theorem.
Their images still distinguish them, and perfect lifting through the central
kernel makes their join the whole source group. Restricting the original
cover gives actual covers onto the marked factors, hence actual central
quotient comparisons.

Source: the central-cover step in Aschbacher–Smith A.2.11, printed p.35.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace PerfectCentralCovering
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite H] in
private theorem pair_semisimple (A B : Subgroup H)
    (hA : IsComponent H A) (hB : IsComponent H B) (hg : A ⊔ B = ⊤) :
    componentLayer H = ⊤ :=
  top_unique (hg ▸ sup_le (le_sSup hA) (le_sSup hB))

theorem Cover.exists_component_pair_lift
    (f : PerfectCentralCovering.Cover G H) (A B : Subgroup H)
    (hA : IsComponent H A) (hB : IsComponent H B) (hne : A ≠ B) (hg : A ⊔ B = ⊤) :
    ∃ C D : Subgroup G, IsComponent G C ∧ IsComponent G D ∧ C ≠ D ∧
      C ⊔ D = ⊤ ∧ C.map f.toMonoidHom = A ∧ D.map f.toMonoidHom = B := by
  let := f.isPerfect
  have hH := pair_semisimple A B hA hB hg
  obtain ⟨C, hC, hmC⟩ := f.exists_component_lift_of_semisimple hH hA
  obtain ⟨D, hD, hmD⟩ := f.exists_component_lift_of_semisimple hH hB
  refine ⟨C, D, hC, hD, (fun he => hne (hmC.symm.trans ((congrArg (map f.toMonoidHom) he).trans hmD))), ?_, hmC, hmD⟩
  apply top_unique
  apply Subgroup.le_of_map_le_of_perfect f.toMonoidHom f.ker_le_center ⊤ (C ⊔ D)
  rw [Subgroup.map_sup, hmC, hmD, hg]
  exact le_top

noncomputable def Cover.restrictComponent (f : PerfectCentralCovering.Cover G H)
    (C : Subgroup G) (A : Subgroup H) (hC : IsComponent G C)
    (hm : C.map f.toMonoidHom = A) : PerfectCentralCovering.Cover C A :=
  let e := MulEquiv.subgroupCongr hm
  { toMonoidHom := e.toMonoidHom.comp (f.toMonoidHom.subgroupMap C)
    surjective := e.surjective.comp (f.toMonoidHom.subgroupMap_surjective C)
    isPerfect := hC.2.toIsPerfect
    ker_le_center := by
      intro x hx
      have hk : (x : G) ∈ f.toMonoidHom.ker := by
        exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_center_iff.mp (f.ker_le_center hk) y) }


end PerfectCentralCovering
