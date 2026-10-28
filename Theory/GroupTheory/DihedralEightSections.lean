module

public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# An elementary-eight section cannot occur under a dihedral-eight Sylow

Let K be a subgroup of a finite group with a dihedral Sylow subgroup of order
eight. If a quotient of K had an elementary Sylow subgroup of order eight,
a Sylow subgroup of K mapping onto it would also have order eight. Its
inclusion into an ambient Sylow and its quotient map would both be bijections.
This would identify the elementary group with the dihedral group, whose
rotation has order four.

This elementary section argument supplies the J₁ and PSL₂(8) exclusions in
Aschbacher--Smith F.6.18, printed p.310.
-/

public section
noncomputable section

open Subgroup
namespace Theory.GroupTheory

/-- Sylow orders decrease through the actual subgroup inclusion and a
surjective homomorphism from that subgroup. -/
theorem sylow_card_section_le
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) (K : Subgroup G) (f : K →* H) (hf : Function.Surjective f)
    (P : Sylow 2 H) : Nat.card P ≤ Nat.card T := by
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf 2 P
  have hPS : Nat.card P ≤ Nat.card S := by
    rw [← hS]
    exact Nat.card_le_card_of_surjective (f.subgroupMap (S : Subgroup K))
      (f.subgroupMap_surjective (S : Subgroup K))
  obtain ⟨U, hU⟩ := (S.isPGroup'.map K.subtype).exists_le_sylow
  have hSU : Nat.card S ≤ Nat.card U := by
    rw [← Subgroup.card_map_of_injective (K := (S : Subgroup K)) K.subtype_injective]
    exact Nat.le_of_dvd (Nat.card_pos (α := U)) (Subgroup.card_dvd_of_le hU)
  exact (hPS.trans hSU).trans_eq (Nat.card_congr (U.equiv T).toEquiv)

/-- An actual quotient of a subgroup cannot have an elementary Sylow of order
eight when the ambient Sylow two-subgroup is dihedral of order eight. -/
theorem not_elementary_eight_sylow_section
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) (eT : T ≃* DihedralGroup 4)
    (K : Subgroup G) (f : K →* H) (hf : Function.Surjective f)
    (P : Sylow 2 H) [IsElementaryAbelian 2 P] (hP : Nat.card P = 8) : False := by
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf 2 P
  let eQ : ((S : Subgroup K).map f) ≃* P :=
    MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hS)
  let q : S →* P := eQ.toMonoidHom.comp (f.subgroupMap (S : Subgroup K))
  have hq : Function.Surjective q :=
    eQ.surjective.comp (f.subgroupMap_surjective (S : Subgroup K))
  obtain ⟨U, hU⟩ := (S.isPGroup'.map K.subtype).exists_le_sylow
  let i : S →* U := (Subgroup.inclusion hU).comp
    (K.subtype.subgroupMap (S : Subgroup K))
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : U => (u : G)) h
  let eU : U ≃* DihedralGroup 4 := (U.equiv T).trans eT
  have hUc : Nat.card U = 8 := by
    rw [Nat.card_congr eU.toEquiv, DihedralGroup.nat_card]
  have hSc : Nat.card S = 8 := by
    apply le_antisymm
    · exact (Nat.card_le_card_of_injective i hi).trans_eq hUc
    · exact hP ▸ Nat.card_le_card_of_surjective q hq
  let eq : S ≃* P := MulEquiv.ofBijective q
    ((Nat.bijective_iff_surjective_and_card q).mpr ⟨hq, hSc.trans hP.symm⟩)
  let ei : S ≃* U := MulEquiv.ofBijective i
    ((Nat.bijective_iff_injective_and_card i).mpr ⟨hi, hSc.trans hUc.symm⟩)
  let e : P ≃* DihedralGroup 4 := (eq.symm.trans ei).trans eU
  let : IsElementaryAbelian 2 (DihedralGroup 4) :=
    IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  have hr := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (DihedralGroup 4)) (DihedralGroup.r 1)
  exact (by decide : (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 ≠ 1) hr

end Theory.GroupTheory
