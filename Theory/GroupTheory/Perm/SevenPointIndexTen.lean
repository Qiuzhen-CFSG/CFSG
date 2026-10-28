module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# The seven-point obstruction

A subgroup of S₇ whose order is divisible by seven acts transitively, hence
primitively. If nine also divides its order, Sylow conjugacy supplies a
three-cycle and Jordan's theorem forces it to contain A₇. In particular S₇
has no subgroup of order 504, or equivalently of index ten.

This is the permutation-group contradiction in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March
2004, Lemma 16.5.12, printed p.1201. The disjoint-cycle Sylow construction
also occurs in the project's primitive-seven order calculation; no simple
group classification is used here.
-/

namespace Theory.GroupTheory.SevenPoint

open Equiv.Perm Subgroup MulAction

private abbrev CyclePair := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

private def leftThreeCycle : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 0 2

private def rightThreeCycle : Equiv.Perm (Fin 7) := Equiv.swap 3 4 * Equiv.swap 3 5

private def cyclePairHom : CyclePair →* Equiv.Perm (Fin 7) where
  toFun a := leftThreeCycle ^ a.1.toAdd.val * rightThreeCycle ^ a.2.toAdd.val
  map_one' := by decide
  map_mul' := by decide

private theorem cyclePairHom_injective : Function.Injective cyclePairHom := by decide

private theorem card_cyclePair_range : Nat.card cyclePairHom.range = 9 := by
  rw [Nat.card_congr (MonoidHom.ofInjective cyclePairHom_injective).symm.toEquiv]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card]

private def standardSylowThree : Sylow 3 (Equiv.Perm (Fin 7)) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact Sylow.ofCard cyclePairHom.range (by
    rw [card_cyclePair_range, Nat.card_perm, Nat.card_fin]
    decide +kernel)

private theorem leftThreeCycle_mem : leftThreeCycle ∈ standardSylowThree := by
  change leftThreeCycle ∈ cyclePairHom.range
  exact ⟨(Multiplicative.ofAdd 1, 1), by decide⟩

/-- In degree seven, divisibility by seven forces transitivity. -/
public theorem pretransitive_of_seven_dvd (U : Subgroup (Equiv.Perm (Fin 7)))
    (h7 : 7 ∣ Nat.card U) : IsPretransitive U (Fin 7) := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := U) 7 h7
  have ho : orderOf (x : Equiv.Perm (Fin 7)) = 7 := by
    simpa only [Subgroup.orderOf_coe] using hx
  have hc : (x : Equiv.Perm (Fin 7)).IsCycle :=
    isCycle_of_prime_order'' (by decide) (by simpa using ho)
  have hs : (x : Equiv.Perm (Fin 7)).support = Finset.univ :=
    (Finset.card_eq_iff_eq_univ _).mp (by simpa using hc.orderOf.symm.trans ho)
  constructor
  intro a b
  have hn (c : Fin 7) : (x : Equiv.Perm (Fin 7)) c ≠ c :=
    mem_support.mp (by rw [hs]; exact Finset.mem_univ c)
  obtain ⟨n, hn⟩ := hc.exists_pow_eq (hn a) (hn b)
  exact ⟨x ^ n, hn⟩

/-- A seven-point group with both prime divisors seven and a full Sylow
three-subgroup contains the alternating group. -/
public theorem alternating_le_of_seven_and_nine_dvd
    (U : Subgroup (Equiv.Perm (Fin 7))) (h7 : 7 ∣ Nat.card U)
    (h9 : 9 ∣ Nat.card U) : alternatingGroup (Fin 7) ≤ U := by
  classical
  let : IsPretransitive U (Fin 7) := pretransitive_of_seven_dvd U h7
  have hp : IsPreprimitive U (Fin 7) := IsPreprimitive.of_prime_card (by
    rw [Nat.card_fin]; decide)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) h9
  let K := H.map U.subtype
  have hK : Nat.card K = 9 := by
    rw [Subgroup.card_map_of_injective U.subtype_injective, hH]
    norm_num
  let T : Sylow 3 (Equiv.Perm (Fin 7)) :=
    Sylow.ofCard K (by rw [hK, Nat.card_perm, Nat.card_fin]; decide +kernel)
  obtain ⟨g, hg⟩ := exists_smul_eq (Equiv.Perm (Fin 7)) standardSylowThree T
  have hmem : g * leftThreeCycle * g⁻¹ ∈ K := by
    have hm := Subgroup.smul_mem_pointwise_smul leftThreeCycle (MulAut.conj g)
      (standardSylowThree : Subgroup _) leftThreeCycle_mem
    change g * leftThreeCycle * g⁻¹ ∈
      (g • standardSylowThree : Sylow 3 (Equiv.Perm (Fin 7))) at hm
    rwa [hg] at hm
  have hKU : K ≤ U := Subgroup.map_subtype_le _
  apply alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hp _ (hKU hmem)
  change (g * leftThreeCycle * g⁻¹).cycleType = {3}
  rw [cycleType_conj]
  exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

public theorem card_ne_504 (U : Subgroup (Equiv.Perm (Fin 7))) : Nat.card U ≠ 504 := by
  intro hc
  have hle := alternating_le_of_seven_and_nine_dvd U (by rw [hc]; decide)
    (by rw [hc]; decide)
  have hd := Subgroup.card_dvd_of_le hle
  rw [nat_card_alternatingGroup, Nat.card_fin, hc] at hd
  norm_num [Nat.factorial] at hd

/-- The exact index-ten contradiction used in 16.5.12. -/
public theorem index_ne_ten (U : Subgroup (Equiv.Perm (Fin 7))) : U.index ≠ 10 := by
  intro hi
  have hc := U.index_mul_card
  rw [hi, Nat.card_perm, Nat.card_fin] at hc
  norm_num [Nat.factorial] at hc
  exact card_ne_504 U (by omega)

/-- A faithful seven-point action cannot have order 2³·3²·7. -/
public theorem no_faithful_action_of_card_504 {M : Type*} [Group M]
    (hM : Nat.card M = 504) (f : M →* Equiv.Perm (Fin 7))
    (hf : Function.Injective f) : False := by
  apply card_ne_504 f.range
  rw [Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv, hM]

end Theory.GroupTheory.SevenPoint
