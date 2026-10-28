module
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection
public import Theory.GroupTheory.CComponent.SolvableQuotient
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# A faithful local component forces central two-core

Let X be an intrinsic C-component and J a C-component in its join with
one full Sylow two-subgroup. If the projection X → X/O₂(X) is injective
on J, then [J,O₂(X)] = 1: the commutator belongs to both J and O₂(X).
The normal centralizer of O₂(X) contains the nonsolvable J, so the
minimality of X makes this centralizer all of X.

Source: C-component calculus in Aschbacher–Smith A.3.3(1), applied to
the natural-block overcomponent in 10.2.3(4), printed p.747.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- Faithfulness of a local C-component modulo the two-core forces that
core into the center of the intrinsic containing C-component. -/
theorem twoCore_le_center_of_faithful_local_component
    {X : Type*} [Group X] [Finite X]
    (hX : (⊤ : Subgroup X).IsCComponent)
    (P : Sylow 2 X) (J : Subgroup X) (hJ : (J.subgroupOf (J ⊔ (P : Subgroup X))).IsCComponent)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 X)).comp J.subtype)) :
    pCore 2 X ≤ center X := by
  let Q := pCore 2 X
  let Y := J ⊔ (P : Subgroup X)
  have hQY : Q ≤ Y := (pCore_isPGroup.le_sylow_of_normal P).trans le_sup_right
  have hJY : J ≤ Y := le_sup_left
  let : (Q.subgroupOf Y).Normal := inferInstance
  let : Group.IsNilpotent (Q.subgroupOf Y) :=
    (pCore_isPGroup (p := 2) (G := X)).comap_subtype.isNilpotent
  have hcomm : ⁅J.subgroupOf Y,Q.subgroupOf Y⁆ = ⊥ := by
    apply bot_unique
    intro x hx
    have hj := hJ.commutator_le_of_solvable (Q.subgroupOf Y)
      (by rw [normalizer_eq_top]; exact le_top) hx
    have hq := commutator_le_right (J.subgroupOf Y) (Q.subgroupOf Y) hx
    have hzero : (⟨(x : X),hj⟩ : J) = 1 := by
      apply hi
      change QuotientGroup.mk' Q (x : X) = QuotientGroup.mk' Q (1 : X)
      rw [map_one]
      exact (QuotientGroup.eq_one_iff _).mpr hq
    exact mem_bot.mpr (Subtype.ext (congrArg J.subtype hzero))
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
  have hc : (⊤ : Subgroup X) ≤ centralizer (Q : Set X) :=
    hX.le_normal_of_nonsolvable_subgroup hnot le_top hJC
  intro q hq
  exact mem_center_iff.mpr (fun x => (hc (mem_top x) q hq).symm)

end Theory.GroupTheory
