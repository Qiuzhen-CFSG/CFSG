module
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.Representation.SLThreeCentralExtension.Involutions
public import Mathlib.GroupTheory.Sylow

/-!
# An involution in every cubic normalizer of SL₃(2)

Two explicit binary matrices generate S₃. Sylow conjugacy transports its
involution to every Sylow three-normalizer. Only the two matrix relations
are checked by reduction; no exhaustive subgroup enumeration is used.
Source: the SL₃(2) local geometry in Aschbacher--Smith 12.4.8, p.815.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace BinaryLinearThree
private def cubic : Group := ⟨!![0,1,0;1,1,0;0,0,1], by decide⟩
private def inverter : Group := ⟨!![1,1,0;0,1,0;0,0,1], by decide⟩
private theorem cubic_order : orderOf cubic = 3 :=
  orderOf_eq_prime (by decide : cubic ^ 3 = 1) (by decide : cubic ≠ 1)
private theorem inverter_order : orderOf inverter = 2 :=
  orderOf_eq_prime (by decide : inverter ^ 2 = 1) (by decide : inverter ≠ 1)
private theorem inverter_normalizes : inverter ∈ normalizer (zpowers cubic : Set Group) := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  have he : MulAut.conj inverter cubic = cubic⁻¹ := by decide
  change zpowers (MulAut.conj inverter cubic) = zpowers cubic
  rw [he, zpowers_inv]

/-- Every Sylow three-normalizer in the actual matrix group contains an
actual involution. -/
theorem exists_involution_normalizing_sylow_three (P : Sylow 3 Group) :
    ∃ b : Group, orderOf b = 2 ∧ b ∈ normalizer (P : Set Group) := by
  let X := zpowers cubic
  have hX : Nat.card X = 3 := (Nat.card_zpowers cubic).trans cubic_order
  have hp : IsPGroup 3 X := (isPGroup_iff_card_dvd_pow).mpr ⟨1,by rw [hX]; decide⟩
  have hi : X.index = 56 := by
    have h := X.card_mul_index
    rw [hX, Matrix.PSL3Two.card_SL] at h
    omega
  let S : Sylow 3 Group := hp.toSylow (by rw [hi]; decide)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Group S P
  have hm : (S : Subgroup Group).map (MulAut.conj g).toMonoidHom = (P : Subgroup Group) := by
    exact congrArg Sylow.toSubgroup hg
  refine ⟨MulAut.conj g inverter, ?_, ?_⟩
  · exact (MulAut.conj g).orderOf_eq inverter |>.trans inverter_order
  · have hn := (S : Subgroup Group).le_normalizer_map (MulAut.conj g).toMonoidHom
    rw [hm] at hn
    exact hn (mem_map_of_mem _ inverter_normalizes)
end BinaryLinearThree
