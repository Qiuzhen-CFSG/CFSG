module
public import Theory.Representation.BinaryPermutation.SevenSourceCubics

/-!
# Three independent pair words for the source cubic

The rotation of the three pairs has an S₃ quotient over the standard
Sylow two-subgroup. Its orbit of the word on {0,1} consists of the three
disjoint pair words. Coordinate evaluations prove their independence,
and hence the rank-three lower bound used in original 14.7.50.
Source: Aschbacher–Smith, printed p.1065, refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Equiv Representation
open scoped BigOperators
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
namespace BinaryPermutation.SevenSourceSpan
abbrev S7 := Perm (Fin 7)
def cycle : S7 := (swap 0 2 * swap 1 3) * (swap 2 4 * swap 3 5)
def axis : Subgroup S7 := zpowers cycle
theorem cycle_order : orderOf cycle = 3 :=
  orderOf_eq_prime (by decide : cycle ^ 3 = 1) (by decide)
theorem axis_card : Nat.card axis = 3 := (Nat.card_zpowers cycle).trans cycle_order

private theorem cubic_join_quotient (r : S7) (hr : orderOf r = 3)
    (P : Subgroup S7) (hSP : standardTwo ≤ P) (hrP : r ∈ P)
    (hP : Nat.card P = 48) (t : S7) (ht : t ∈ standardTwo)
    (hnt : r * t * r⁻¹ ∉ standardTwo) :
    Nonempty (((zpowers r ⊔ standardTwo : Subgroup S7) ⧸
      pCore 2 (zpowers r ⊔ standardTwo : Subgroup S7)) ≃* Perm (Fin 3)) := by
  let J := zpowers r ⊔ standardTwo
  have hJP : J ≤ P := sup_le (zpowers_le.mpr hrP) hSP
  have hSJ : standardTwo ≤ J := le_sup_right
  have h3 : 3 ∣ Nat.card J := by
    have hh := card_dvd_of_le (show zpowers r ≤ J from le_sup_left)
    rwa [Nat.card_zpowers,hr] at hh
  have h16 : 16 ∣ Nat.card J := standardTwo_card ▸ card_dvd_of_le hSJ
  have hd : 48 ∣ Nat.card J :=
    (show Nat.Coprime 3 16 by decide).mul_dvd_of_dvd_of_dvd h3 h16
  have hj : Nat.card J = 48 := le_antisymm
    (hP ▸ card_le_of_le hJP) (Nat.le_of_dvd Nat.card_pos hd)
  let S := standardSylow.subtype hSJ
  have hs : Nat.card S = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv).trans standardTwo_card
  have hi : (S : Subgroup J).index = 3 := by
    have hh := (S : Subgroup J).card_mul_index
    rw [hs,hj] at hh
    omega
  apply sylow_index_three_core_quotient S hi
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S)
  intro he
  have hn : (S : Subgroup J).Normal := he ▸ inferInstance
  have hnorm : J ≤ normalizer (standardTwo : Set S7) :=
    (normal_subgroupOf_iff_le_normalizer hSJ).mp hn
  exact hnt ((mem_normalizer_iff.mp (hnorm ((show zpowers r ≤ J from le_sup_left) (mem_zpowers r))) t).mp ht)


/-- The pair-rotation actor satisfies the original S₃-over-Sylow hypothesis. -/
theorem axis_join_quotient :
    Nonempty (((axis ⊔ standardTwo : Subgroup S7) ⧸
      pCore 2 (axis ⊔ standardTwo : Subgroup S7)) ≃* Perm (Fin 3)) :=
  cubic_join_quotient cycle cycle_order synthemeOvergroup inf_le_right (by decide)
    synthemeOvergroup_card (swap 2 4 * swap 3 5) (by decide) (by decide)

def point : core (Fin 7) := ⟨![1,1,0,0,0,0,0], by
  change (∑ i : Fin 7, (![1,1,0,0,0,0,0] : Fin 7 → ZMod 2) i) = 0
  decide⟩

/-- The three disjoint pair words are independent by coordinate evaluation. -/
theorem orbit_independent : LinearIndependent (ZMod 2)
    (fun i : Fin 3 => coreRepresentation (Fin 7) (cycle ^ i.val) point) := by
  apply linearIndependent_iff_injective_fintypeLinearCombination.mpr
  intro a b hab
  have hh : (∑ i : Fin 3, a i • coreRepresentation (Fin 7) (cycle ^ i.val) point) =
      (∑ i : Fin 3, b i • coreRepresentation (Fin 7) (cycle ^ i.val) point) := hab
  let ev (j : Fin 3) : core (Fin 7) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj (⟨2*j.val, by omega⟩ : Fin 7)).comp (core (Fin 7)).subtype
  have entries : ∀ i j : Fin 3,
      ev j (coreRepresentation (Fin 7) (cycle ^ i.val) point) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  funext j
  have he := congrArg (ev j) hh
  simpa only [map_sum,map_smul,entries,smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] using he

/-- Any subspace containing the pair orbit has rank at least three. -/
theorem three_le_of_orbit_mem (E : Submodule (ZMod 2) (core (Fin 7)))
    (hm : ∀ i : Fin 3, coreRepresentation (Fin 7) (cycle ^ i.val) point ∈ E) :
    3 ≤ Module.finrank (ZMod 2) E := by
  have hi : LinearIndependent (ZMod 2) (fun i : Fin 3 =>
      (⟨coreRepresentation (Fin 7) (cycle ^ i.val) point,hm i⟩ : E)) :=
    LinearIndependent.of_comp E.subtype orbit_independent
  simpa using hi.fintype_card_le_finrank
end BinaryPermutation.SevenSourceSpan
