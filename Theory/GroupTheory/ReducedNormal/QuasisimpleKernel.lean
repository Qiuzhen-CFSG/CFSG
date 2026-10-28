module

public import Theory.GroupTheory.ReducedNormal.QuasisimpleImage

/-!
# The full reduced-action kernel with a two-group supplement

The normal component has exactly its two-core as kernel on a reduced
noncentral module. If its ambient quotient is a two-group, the full action
kernel is a two-group as well and therefore equals the ambient two-core.

Source: Aschbacher--Smith B.2.10 and the original LS-action in 15.1.27.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]
variable (W K : Subgroup G) [W.Normal] [K.Normal]
variable (hr : IsPReduced 2 W) [IsQuasisimple (K ⧸ pCore 2 K)]
variable (hz : center (K ⧸ pCore 2 K) = ⊥) (hm : ⁅W,K⁆ ≠ ⊥)
include hr hz hm
/-- A two-group supplement makes the full centralizer equal to the ambient two-core. -/
theorem reduced_quasisimple_centralizer_eq_pCore (hquot : IsPGroup 2 (G ⧸ K)) : centralizer (W : Set G) = pCore 2 G := by
  let C := centralizer (W : Set G)
  let f := (QuotientGroup.mk' K).comp C.subtype
  have hk : IsPGroup 2 f.ker := by
    let g : f.ker →* pCore 2 K := {
      toFun x := ⟨⟨x.val.val,(QuotientGroup.eq_one_iff (N := K) _).mp x.property⟩,?_⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    · exact pCore_isPGroup.of_injective g (fun _ _ he => Subtype.ext (Subtype.ext
        (congrArg (fun y : pCore 2 K => ((y : K) : G)) he)))
    · rw [←reduced_quasisimple_subgroupMap_ker W K hr hz hm]
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := C) _).mpr x.val.property
  have hp : IsPGroup 2 C := by
    have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup f hk
    rw [Subgroup.comap_top] at hh
    exact hh.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup C) ≃* C)
  exact le_antisymm (le_sSup ⟨inferInstance,hp⟩)
    (le_centralizer_iff.mp hr.le_centralizer_pCore)
end Theory.GroupTheory
