module
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreAction
public import Theory.GroupTheory.Commutator.PerfectClassTwoAction
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.PGroup.ExtraspecialCentralizer

/-!
# Short local components and extraspecial two-cores

A short local C-component has elementary commutator with the whole two-core.
When that core is extraspecial, a perfect group with abelian displacement
centralizes it. The centralizer condition then puts the component in the
solvable two-core, a contradiction.

This supplies the extraspecial involution-centralizer escape in the paired
alternating-five branch of Aschbacher--Smith 2.4.25, printed p.543. Locality is
at a full Sylow subgroup of this overgroup; no ambient Sylow size is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]
/-- A self-centralizing extraspecial two-core admits no short full-Sylow local component. -/
theorem not_local_short_of_extraspecial_twoCore
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    [IsExtraspecial 2 (pCore 2 G)] (S : Sylow 2 G)
    (A : Subgroup G) (hA : IsShort A) :
    A ∉ ChapterA.Section03.localCComponents S := by
  intro hl
  let H := A ⊔ (S : Subgroup G)
  let e : A.subgroupOf H ≃* A := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect (A.subgroupOf H) := hl.perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let Q := pCore 2 G
  let Z := (center Q).map Q.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZ : Z ≤ center G := central_of_normal_card_two Z (by
    rw [card_map_of_injective Q.subtype_injective, IsExtraspecial.center_order_p 2 Q])
  have hclass : ⁅Q, Q⁆ ≤ Z := by
    rw [← map_subtype_commutator]
    exact map_mono (IsExtraspecial.quotient_elementary_abelian 2 Q).commutator_le_center_of_central_quotient
  have hcenter : Q ⊓ centralizer (Q : Set G) ≤ Z := by
    intro x hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    exact mem_center_iff.mpr (fun y => Subtype.ext (hx.2 y y.property))
  let D := ⁅Q, A⁆
  have hp (x : D) : x ^ 2 = 1 :=
    Subtype.ext (local_short_core_commutator_square S A hA hl x.property)
  have hcom : IsMulCommutative D := ⟨⟨fun x y =>
    (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hp x)) x y).eq⟩⟩
  have hab : ⁅D, D⁆ = ⊥ := by
    rw [← map_subtype_commutator, (commutator_eq_bot_iff D).mpr hcom, Subgroup.map_bot]
  have hbot : ⁅Q, A⁆ = ⊥ := commutator_eq_bot_of_perfect_abelian_classTwo_action Q Z A
    le_normalizer_of_normal hclass hcenter
    (commutator_eq_bot_iff_le_centralizer.mpr (hZ.trans (center_le_centralizer _))) hab
  have hAQ : A ≤ Q := (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp hbot)).trans hself
  have hAp : IsPGroup 2 A := pCore_isPGroup.to_le hAQ
  let : Group.IsNilpotent A := hAp.isNilpotent
  exact hl.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective)
end CFSG.Quasithin.ChapterC
