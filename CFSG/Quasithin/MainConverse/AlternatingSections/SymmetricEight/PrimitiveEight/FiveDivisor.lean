module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.FinCases

/-!
# A factor five in primitive degree eight

A primitive subgroup of S₈ whose order is divisible by five contains A₈.
Cauchy's theorem supplies a five-cycle, since two disjoint five-cycles cannot
fit on eight points. The pointwise stabilizer of its three fixed points is
transitive, hence primitive, on the five remaining points. Jordan's proved
multiple-primitivity criterion therefore makes the whole group four-transitive.

In coordinates where the cycle is `a = (0 1 2 3 4)`, four-transitivity gives a
conjugate `b = (0 1 2 5 y)`. Injectivity leaves exactly `y = 3, 4, 6, 7`.
The words `a²b²ab`, `a⁴b`, and `a²ba²b` produce a three-cycle in these cases;
the four finite calculations are checked by the kernel. The proved three-cycle
theorem of Jordan then supplies A₈. No general prime-cycle theorem or primitive
subgroup catalogue is assumed.

This is a structural ingredient for condition K in Aschbacher--Smith,
*The Classification of Quasithin Groups*, printed pp.4 and 482. The Jordan
criteria used here are formalized in Mathlib from Wielandt,
*Finite Permutation Groups*, §13.
-/

namespace CFSG.Quasithin.MainConverse

open Equiv Equiv.Perm MulAction Subgroup

namespace PrimitiveEight.FiveDivisor

private def a : Perm (Fin 8) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

private def b (y : Fin 8) : Perm (Fin 8) := swap 0 1 * swap 1 2 * swap 2 5 * swap 5 y

private theorem four_transitive (U : Subgroup (Perm (Fin 8))) [IsPreprimitive U (Fin 8)]
    {g : Perm (Fin 8)} (hg : g ∈ U) (hgc : g.IsCycle) (hgo : orderOf g = 5) :
    IsMultiplyPretransitive U (Fin 8) 4 := by
  classical
  have hs : g.support.card = 5 := hgc.orderOf.symm.trans hgo
  have ht := isPretransitive_of_isCycle_mem hgc hg
  have hp : IsPreprimitive (fixingSubgroup U (g.support : Set (Fin 8))ᶜ)
      (SubMulAction.ofFixingSubgroup U (g.support : Set (Fin 8))ᶜ) := by
    apply IsPreprimitive.of_prime_card
    convert (show Nat.Prime 5 by decide) using 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hs]
    congr 1
    ext x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]
  have hm : IsMultiplyPreprimitive U (Fin 8) 4 := by
    apply IsPreprimitive.isMultiplyPreprimitive (inferInstance : IsPreprimitive U (Fin 8))
      (s := (g.support : Set (Fin 8))ᶜ) (n := 2)
    · have h := Set.ncard_add_ncard_compl (g.support : Set (Fin 8))
      simp only [Set.ncard_coe_finset, hs, Nat.card_fin] at h
      omega
    · simp
    · exact hp
  exact hm.isMultiplyPretransitive

private theorem normalized_threeCycle (H : Subgroup (Perm (Fin 8))) (ha : a ∈ H)
    (k : Perm (Fin 8)) (hk : k ∈ H)
    (h0 : k 0 = 0) (h1 : k 1 = 1) (h2 : k 2 = 2) (h3 : k 3 = 5) :
    ∃ t ∈ H, t.IsThreeCycle := by
  have hb : b (k 4) ∈ H := by
    have he : k * a * k⁻¹ = b (k 4) := by
      change (MulAut.conj k) a = b (k 4)
      simp only [a, map_mul, MulAut.conj_apply, ← swap_apply_apply, h0, h1, h2, h3, b]
    rw [← he]
    exact H.mul_mem (H.mul_mem hk ha) (H.inv_mem hk)
  have hn0 : k 4 ≠ 0 := by rw [← h0]; exact k.injective.ne (by decide)
  have hn1 : k 4 ≠ 1 := by rw [← h1]; exact k.injective.ne (by decide)
  have hn2 : k 4 ≠ 2 := by rw [← h2]; exact k.injective.ne (by decide)
  have hn5 : k 4 ≠ 5 := by rw [← h3]; exact k.injective.ne (by decide)
  generalize k 4 = y at hb hn0 hn1 hn2 hn5
  fin_cases y
  · exact (hn0 rfl).elim
  · exact (hn1 rfl).elim
  · exact (hn2 rfl).elim
  · refine ⟨a * a * b 3 * b 3 * a * b 3, ?_, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem ha ha) hb) hb) ha) hb
    · apply card_support_eq_three_iff.mp
      decide +kernel
  · refine ⟨a ^ 4 * b 4, H.mul_mem (H.pow_mem ha 4) hb, ?_⟩
    apply card_support_eq_three_iff.mp
    decide +kernel
  · exact (hn5 rfl).elim
  · refine ⟨a * a * b 6 * a * a * b 6, ?_, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem ha ha) hb) ha) ha) hb
    · apply card_support_eq_three_iff.mp
      decide +kernel
  · refine ⟨a * a * b 7 * a * a * b 7, ?_, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem ha ha) hb) ha) ha) hb
    · apply card_support_eq_three_iff.mp
      decide +kernel

private def firstFour : Fin 4 ↪ Fin 8 := ⟨![0, 1, 2, 3], by decide +kernel⟩

private def otherFour : Fin 4 ↪ Fin 8 := ⟨![0, 1, 2, 5], by decide +kernel⟩

private theorem threeCycle_of_four_transitive (U : Subgroup (Perm (Fin 8)))
    [IsMultiplyPretransitive U (Fin 8) 4]
    {g : Perm (Fin 8)} (hg : g ∈ U) (hgc : g.IsCycle) (hgo : orderOf g = 5) :
    ∃ t ∈ U, t.IsThreeCycle := by
  classical
  have hs : g.support.card = 5 := hgc.orderOf.symm.trans hgo
  have hconj : IsConj g a := isConj_iff_cycleType_eq.mpr (by
    rw [hgc.cycleType, hs]
    exact (show a.cycleType = {5} by decide +kernel).symm)
  obtain ⟨e, he⟩ := isConj_iff.mp hconj
  let H := U.map (MulAut.conj e).toMonoidHom
  have ha : a ∈ H := Subgroup.mem_map.mpr ⟨g, hg, he⟩
  obtain ⟨h, hh⟩ := exists_smul_eq U
    (firstFour.trans e.symm.toEmbedding) (otherFour.trans e.symm.toEmbedding)
  let k : Perm (Fin 8) := e * (h : Perm (Fin 8)) * e⁻¹
  have hk : k ∈ H := Subgroup.mem_map.mpr ⟨h, h.property, rfl⟩
  have hv (i : Fin 4) : k (firstFour i) = otherFour i := by
    have hi := congrArg (fun f : Fin 4 ↪ Fin 8 => e (f i)) hh
    simpa only [k, Perm.mul_apply, Perm.inv_def,
      Function.Embedding.smul_apply, Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply, subgroup_smul_def, Perm.smul_def, Equiv.apply_symm_apply]
      using hi
  obtain ⟨t, ht, ht3⟩ := normalized_threeCycle H ha k hk (hv 0) (hv 1) (hv 2) (hv 3)
  obtain ⟨u, hu, hut⟩ := Subgroup.mem_map.mp ht
  refine ⟨u, hu, ?_⟩
  rw [← hut] at ht3
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
    IsThreeCycle, cycleType_conj] using ht3

end PrimitiveEight.FiveDivisor

/-- A primitive subgroup of S₈ with order divisible by five contains A₈. -/
public theorem primitiveEight_alternating_le_of_five_dvd
    (U : Subgroup (Equiv.Perm (Fin 8))) [IsPreprimitive U (Fin 8)]
    (h5 : 5 ∣ Nat.card U) : alternatingGroup (Fin 8) ≤ U := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := U) 5 h5
  have ho : orderOf (g : Perm (Fin 8)) = 5 := by simpa using hg
  have hc : (g : Perm (Fin 8)).IsCycle := isCycle_of_prime_order'
    (by rw [ho]; decide) (by rw [ho]; decide)
  have := PrimitiveEight.FiveDivisor.four_transitive U g.property hc ho
  obtain ⟨t, ht, ht3⟩ := PrimitiveEight.FiveDivisor.threeCycle_of_four_transitive U g.property hc ho
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem inferInstance ht3 ht

end CFSG.Quasithin.MainConverse
