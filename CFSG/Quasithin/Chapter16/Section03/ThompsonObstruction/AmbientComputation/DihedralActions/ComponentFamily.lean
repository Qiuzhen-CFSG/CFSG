module
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.LocalComputation
public import Theory.GroupTheory.TwoElementaryIndexTwo
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# The two maximum elementary subgroups of the component factor

The standard D₈ factor has two elementary four-groups. Their index-two
covering property excludes every other maximum elementary subgroup, and
reflections show that the two four-groups generate D₈. Transport through an
actual component equivalence retains their inclusions in the ambient group.

We reuse the concrete four-groups from LocalComputation. This calculation
is independent of its wreath-product Thompson conclusion.
Source: Aschbacher--Smith, 16.3.12, printed p.1182 / PDF p.1199.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup Stellmacher
open LocalComputation

private theorem four_elementary (i : Fin 2) : IsElementaryAbelian 2 (dihedralFour i) where
  toIsMulCommutative := ⟨⟨fun a b =>
    (Commute.of_orderOf_dvd_two (fun x : dihedralFour i => orderOf_dvd_of_pow_eq_one
      (show x ^ 2 = 1 from Subtype.ext (dihedralFour_square i x x.property))) a b).eq⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    (fun x => Subtype.ext (dihedralFour_square i x x.property))

private theorem four_index (i : Fin 2) : (dihedralFour i).index = 2 := by
  have h := (dihedralFour i).card_mul_index
  rw [dihedralFour_card, DihedralGroup.nat_card] at h
  omega

private theorem four_ne : dihedralFour 0 ≠ dihedralFour 1 := by
  intro h
  have hm : DihedralGroup.sr 0 ∈ dihedralFour 0 := by decide
  rw [h] at hm
  exact (by decide : DihedralGroup.sr 0 ∉ dihedralFour 1) hm

private theorem d8_not_elementary : ¬ IsElementaryAbelian 2 (DihedralGroup 4) := by
  intro h
  have he : (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 _) _
  exact (by decide : (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 ≠ 1) he

/-- The two four-groups cover every elementary subgroup of the component model. -/
theorem componentModel_elementary_cover (E : Subgroup (DihedralGroup 4))
    (hE : IsElementaryAbelian 2 E) : ∃ i : Fin 2, E ≤ dihedralFour i := by
  rcases elementary_le_one_of_two_index_two (dihedralFour 0) (dihedralFour 1)
      (four_elementary 0) (four_elementary 1) (four_index 0) (four_index 1)
      four_ne d8_not_elementary E hE with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

theorem componentModel_four_maximal (i : Fin 2) :
    dihedralFour i ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (DihedralGroup 4)) := by
  refine ⟨le_top, four_elementary i, ?_⟩
  intro E _ hE
  obtain ⟨j, hj⟩ := componentModel_elementary_cover E hE
  calc Nat.card E ≤ Nat.card (dihedralFour j) := card_le_of_le hj
    _ = Nat.card (dihedralFour i) := (dihedralFour_card j).trans (dihedralFour_card i).symm

/-- Exactly the two four-groups constitute the maximum-order family in D₈. -/
theorem componentModel_maxFamily_iff (E : Subgroup (DihedralGroup 4)) :
    E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (DihedralGroup 4)) ↔
      ∃ i : Fin 2, E = dihedralFour i := by
  constructor
  · intro hE
    obtain ⟨i, hi⟩ := componentModel_elementary_cover E hE.2.1
    exact ⟨i, eq_of_le_of_card_ge hi (hE.2.2 _ le_top (four_elementary i))⟩
  · rintro ⟨i, rfl⟩
    exact componentModel_four_maximal i

/-- These maximum four-groups generate the actual dihedral component. -/
theorem componentModel_maxJ : elementaryAbelianMaxJ (⊤ : Subgroup (DihedralGroup 4)) = ⊤ := by
  apply top_unique
  intro x _
  have href : ∀ i : ZMod 4, DihedralGroup.sr i ∈
      elementaryAbelianMaxJ (⊤ : Subgroup (DihedralGroup 4)) := by
    intro i
    have h : DihedralGroup.sr i ∈ dihedralFour 0 ∨ DihedralGroup.sr i ∈ dihedralFour 1 := by
      revert i
      decide +kernel
    rcases h with h | h
    · exact (le_sSup (componentModel_four_maximal 0)) h
    · exact (le_sSup (componentModel_four_maximal 1)) h
  cases x with
  | r i =>
    have h := (elementaryAbelianMaxJ (⊤ : Subgroup (DihedralGroup 4))).mul_mem (href 0) (href i)
    simpa only [DihedralGroup.sr_mul_sr, sub_zero] using h
  | sr i => exact href i

variable {G : Type*} [Group G]

/-- The marked four-groups of any actual dihedral component. -/
def componentFour (C : Subgroup G) (e : C ≃* DihedralGroup 4) (i : Fin 2) : Subgroup G :=
  (dihedralFour i).map (C.subtype.comp e.symm.toMonoidHom)

/-- Transport of the exact two-member family through a component marking. -/
theorem component_maxFamily_iff (C : Subgroup G) (e : C ≃* DihedralGroup 4) (A : Subgroup G) :
    A ∈ elementaryAbelianMaxSubgroups C ↔ ∃ i : Fin 2, A = componentFour C e i := by
  rw [maxFamily_equiv_iff C e.symm]
  constructor
  · rintro ⟨B, hB, hA⟩
    obtain ⟨i, rfl⟩ := (componentModel_maxFamily_iff B).mp hB
    exact ⟨i, hA⟩
  · rintro ⟨i, rfl⟩
    exact ⟨dihedralFour i, componentModel_four_maximal i, rfl⟩

/-- The maximum elementary subgroups generate the dihedral component itself. -/
theorem component_maxJ (C : Subgroup G) (e : C ≃* DihedralGroup 4) :
    elementaryAbelianMaxJ C = C := by
  let f := C.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := C.subtype_injective.comp e.symm.injective
  have hr : (⊤ : Subgroup (DihedralGroup 4)).map f = C := by
    ext x
    constructor
    · rintro ⟨a, _, rfl⟩
      exact (e.symm a).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, mem_top _, congrArg Subtype.val (e.symm_apply_apply _)⟩
  calc elementaryAbelianMaxJ C =
      (elementaryAbelianMaxJ (⊤ : Subgroup (DihedralGroup 4))).map f := by
        rw [← elementaryAbelianMaxJ_map_injective f hf, hr]
    _ = C := by rw [componentModel_maxJ, hr]

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
