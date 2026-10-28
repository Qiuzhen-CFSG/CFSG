module
public import Theory.GroupTheory.CComponent.LocalFaithfulCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure

/-!
# Central two-core forced by a quasisimple local component

Let X be an intrinsic C-component, and let J be a quasisimple C-component
in its join with a full Sylow two-subgroup of X. The component-normal-subgroup
dichotomy makes J centralize O₂(X). This centralizer is normal in X and
contains the nonsolvable J, so C-component minimality makes it all of X.
Consequently O₂(X) is central. No faithfulness modulo that core is assumed.

Source application: Aschbacher–Smith, original 12.2.25, printed p.805,
to the actual containing image in N_G(C_T(U))/C_T(U).
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- An intrinsic C-component containing a quasisimple full-Sylow local
component has central two-core. -/
theorem twoCore_le_center_of_quasisimple_local_component
    {X : Type*} [Group X] [Finite X]
    (hX : (⊤ : Subgroup X).IsCComponent)
    (P : Sylow 2 X) (J : Subgroup X)
    (hJ : (J.subgroupOf (J ⊔ (P : Subgroup X))).IsCComponent)
    [IsQuasisimple J] : pCore 2 X ≤ center X := by
  let Q := pCore 2 X
  let Y := J ⊔ (P : Subgroup X)
  have hQY : Q ≤ Y := (pCore_isPGroup.le_sylow_of_normal P).trans le_sup_right
  have hJY : J ≤ Y := le_sup_left
  let : (Q.subgroupOf Y).Normal := inferInstance
  let : Group.IsNilpotent (Q.subgroupOf Y) :=
    (pCore_isPGroup (p := 2) (G := X)).comap_subtype.isNilpotent
  let : IsQuasisimple (J.subgroupOf Y) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hJY).symm
  have hc : IsComponent Y (J.subgroupOf Y) := ⟨hJ.subnormal, inferInstance⟩
  have hcomm : ⁅J.subgroupOf Y,Q.subgroupOf Y⁆ = ⊥ := by
    apply (hc.normal_dichotomy (Q.subgroupOf Y)).resolve_left
    intro hle
    exact hJ.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hle) (inclusion_injective hle))
  have hJC : J ≤ centralizer (Q : Set X) := by
    intro j hj q hq
    exact congrArg Subtype.val ((commutator_eq_bot_iff_le_centralizer.mp hcomm)
      (show (⟨j,hJY hj⟩ : Y) ∈ J.subgroupOf Y from hj)
      ⟨q,hQY hq⟩ hq)
  have hnot : ¬ Group.IsSolvable J := by
    intro hs
    let : Group.IsSolvable J := hs
    exact hJ.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hJY).toMonoidHom)
        (subgroupOfEquivOfLe hJY).injective)
  have ht : (⊤ : Subgroup X) ≤ centralizer (Q : Set X) :=
    hX.le_normal_of_nonsolvable_subgroup hnot le_top hJC
  intro q hq
  exact mem_center_iff.mpr (fun x => (ht (mem_top x) q hq).symm)

end Theory.GroupTheory
