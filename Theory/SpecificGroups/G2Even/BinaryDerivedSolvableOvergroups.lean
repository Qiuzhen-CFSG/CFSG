module

public import Theory.AtlasPort.LinearGroups.G2.BinaryProperSylowCore
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Theory.GroupTheory.SolvableSylowOvergroups
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.TwoGroupExclusion.Solvability

/-!
# Solvable proper Sylow overgroups in G₂(2)′

A Sylow two-subgroup has order 32. The proper-overgroup index divides 189;
simplicity excludes indices three and seven, and the proved nine-point
obstruction excludes index nine. The remaining orders are 288, 224, 96 and
32. The two-prime theorem handles the orders involving only two and three.
At order 224 a cyclic subgroup of order seven has prime-power index, so
Burnside's proved solvability theorem applies.

This uses the actual binary octonion commutator group. Source/application:
Aschbacher–Smith, 13.1.2(5), printed p.866. Concrete group computations are
inherited from the licensed ATLAS port; see LICENSES/ATLAS.txt.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2
local notation "D" => commutator (Model (ZMod 2))

private theorem card_derived : Nat.card D = 6048 :=
  DerivedEvenOrder.card_derived_binary (by simp)

private theorem card_sylow (S : Sylow 2 D) : Nat.card S = 32 := by
  rw [S.card_eq_multiplicity,card_derived]
  decide +kernel

private theorem solvable_of_card_224 {H : Type*} [Group H] [Finite H]
    (hc : Nat.card H = 224) : Group.IsSolvable H := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let P : Sylow 7 H := Classical.choice inferInstance
  have hP : Nat.card P = 7 := by
    rw [P.card_eq_multiplicity,hc]
    decide +kernel
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hi : (P : Subgroup H).index = 2 ^ 5 := by
    have he := (P : Subgroup H).card_mul_index
    rw [hP,hc] at he
    omega
  exact (P : Subgroup H).isSolvable_of_isMulCommutative_of_prime_power_index
    Nat.prime_two hi

private theorem solvable_of_card_dvd_288 {H : Type*} [Group H] [Finite H]
    (hc : Nat.card H ∣ 288) : Group.IsSolvable H := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  have h : p ∣ 2 ^ 5 * 3 ^ 2 := hd.trans hc
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      |>.resolve_left hp.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
      |>.resolve_left hp.ne_one)

/-- Proper Sylow overgroups of the actual G₂(2)′ carrier are solvable. -/
theorem binaryDerived_solvableSylowOvergroups : SolvableSylowOvergroups D := by
  let : IsSimpleGroup D := isSimple_commutator_binary
  intro S H hSH hH
  have h32 : 32 ∣ Nat.card H := by
    rw [←card_sylow S]
    exact card_dvd_of_le hSH
  obtain ⟨k,hk⟩ := h32
  have he := H.card_mul_index
  rw [card_derived,hk] at he
  have hi189 : H.index ∣ 189 := ⟨k,by nlinarith⟩
  have hi : H.index ∈ [1,3,7,9,21,27,63,189] := by
    have hb := Nat.le_of_dvd (by decide : 0 < 189) hi189
    exact (by decide +kernel : ∀ i : Fin 190, i.val ∣ 189 →
      i.val ∈ [1,3,7,9,21,27,63,189]) ⟨H.index,by omega⟩ hi189
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  have hp := H.one_lt_index_of_ne_top hH
  rcases hi with hi | hi | hi | hi | hi | hi | hi | hi
  · omega
  · exact False.elim (hH (Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt H
      (by rw [hi,card_derived]; decide)))
  · exact False.elim (hH (Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt H
      (by rw [hi,card_derived]; decide)))
  · exact False.elim (BinaryProperSylowCore.index_ne_nine H hi)
  · apply solvable_of_card_dvd_288
    have hc : Nat.card H = 288 := by
      have he := H.card_mul_index
      rw [hi,card_derived] at he
      omega
    rw [hc]
  · apply solvable_of_card_224
    have he := H.card_mul_index
    rw [hi,card_derived] at he
    omega
  · apply solvable_of_card_dvd_288
    have hc : Nat.card H = 96 := by
      have he := H.card_mul_index
      rw [hi,card_derived] at he
      omega
    rw [hc]; decide
  · apply solvable_of_card_dvd_288
    have hc : Nat.card H = 32 := by
      have he := H.card_mul_index
      rw [hi,card_derived] at he
      omega
    rw [hc]; decide
end Atlas.G2
