module

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.ActionBasics

/-!
# Excluding the prime five in a proper primitive subgroup of A₉

A five-cycle makes a primitive degree-nine action five-transitive by Jordan's
proved multiple-primitivity criterion. Conjugating it to a cycle with four common
entries produces a three-cycle, so Jordan's three-cycle theorem supplies A₉.
The two small permutation identities are checked by the kernel.

This is an action ingredient for condition K in the alternating case of
Aschbacher–Smith, *The Classification of Quasithin Groups*, `refs/quasithin.pdf`,
printed pp.4 and 482. It does not use the unproved general prime-cycle version
of Jordan's theorem or a catalogue of primitive groups.
-/

open Equiv Equiv.Perm MulAction Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.MainConverse.NineReduction

private def fiveCycle : Perm (Fin 9) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4
private def otherFiveCycle : Perm (Fin 9) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 5
private def firstFive : Fin 5 ↪ Fin 9 := ⟨![0, 1, 2, 3, 4], by decide⟩
private def otherFive : Fin 5 ↪ Fin 9 := ⟨![0, 1, 2, 3, 5], by decide⟩

private theorem threeCycle_of_five_transitive (U : Subgroup (Perm (Fin 9)))
    [IsMultiplyPretransitive U (Fin 9) 5]
    {g : Perm (Fin 9)} (hg : g ∈ U) (hgc : g.IsCycle) (hgo : orderOf g = 5) :
    ∃ t ∈ U, t.IsThreeCycle := by
  classical
  have hs : g.support.card = 5 := hgc.orderOf.symm.trans hgo
  have hconj : IsConj g fiveCycle := isConj_iff_cycleType_eq.mpr (by
    rw [hgc.cycleType, hs]
    exact (show fiveCycle.cycleType = {5} by decide +kernel).symm)
  obtain ⟨e, he⟩ := isConj_iff.mp hconj
  let V := U.map (MulAut.conj e).toMonoidHom
  have ha : fiveCycle ∈ V := Subgroup.mem_map.mpr ⟨g, hg, he⟩
  obtain ⟨h, hh⟩ := exists_smul_eq U
    (firstFive.trans e.symm.toEmbedding) (otherFive.trans e.symm.toEmbedding)
  let k : Perm (Fin 9) := e * (h : Perm (Fin 9)) * e⁻¹
  have hk : k ∈ V := Subgroup.mem_map.mpr ⟨h, h.property, rfl⟩
  have hv (i : Fin 5) : k (firstFive i) = otherFive i := by
    have hi := congrArg (fun f : Fin 5 ↪ Fin 9 => e (f i)) hh
    simpa only [k, Perm.mul_apply, Perm.inv_def,
      Function.Embedding.smul_apply, Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply, subgroup_smul_def, Perm.smul_def, Equiv.apply_symm_apply]
      using hi
  have hb : otherFiveCycle ∈ V := by
    have heq : k * fiveCycle * k⁻¹ = otherFiveCycle := by
      change (MulAut.conj k) fiveCycle = otherFiveCycle
      have h0 := hv 0
      have h1 := hv 1
      have h2 := hv 2
      have h3 := hv 3
      have h4 := hv 4
      change k 0 = 0 at h0
      change k 1 = 1 at h1
      change k 2 = 2 at h2
      change k 3 = 3 at h3
      change k 4 = 5 at h4
      simp only [fiveCycle, map_mul, MulAut.conj_apply, ← swap_apply_apply,
        h0, h1, h2, h3, h4, otherFiveCycle]
    rw [← heq]
    exact V.mul_mem (V.mul_mem hk ha) (V.inv_mem hk)
  have ht : fiveCycle⁻¹ * otherFiveCycle ∈ V := V.mul_mem (V.inv_mem ha) hb
  have ht3 : (fiveCycle⁻¹ * otherFiveCycle).IsThreeCycle := by
    apply card_support_eq_three_iff.mp
    decide +kernel
  obtain ⟨u, hu, hut⟩ := Subgroup.mem_map.mp ht
  refine ⟨u, hu, ?_⟩
  rw [← hut] at ht3
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
    IsThreeCycle, cycleType_conj] using ht3

private theorem five_transitive_of_five_dvd (U : Subgroup (Perm (Fin 9)))
    (hp : IsPreprimitive U (Fin 9)) (hfive : 5 ∣ Nat.card U) :
    IsMultiplyPretransitive U (Fin 9) 5 := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  have hgo : orderOf (g : Perm (Fin 9)) = 5 := by simpa using hg
  have hgc : (g : Perm (Fin 9)).IsCycle :=
    Perm.isCycle_of_prime_order' (hgo ▸ by decide) (by simp; omega)
  have hsupp : (g : Perm (Fin 9)).support.card = 5 := hgc.orderOf.symm.trans hgo
  have hsc : ((g : Perm (Fin 9)).supportᶜ : Set (Fin 9)).ncard = 3 + 1 := by
    have := Set.ncard_add_ncard_compl ((g : Perm (Fin 9)).support : Set (Fin 9))
    simp only [Set.ncard_coe_finset, hsupp, Nat.card_fin] at this
    omega
  have := Perm.isPretransitive_of_isCycle_mem hgc g.property
  have hprim : IsPreprimitive
      (fixingSubgroup U ((g : Perm (Fin 9)).supportᶜ : Set (Fin 9)))
      (SubMulAction.ofFixingSubgroup U ((g : Perm (Fin 9)).supportᶜ : Set (Fin 9))) := by
    apply IsPreprimitive.of_prime_card
    convert Nat.prime_five using 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hsupp]
    apply congr_arg Finset.card
    ext x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]
  exact (hp.isMultiplyPreprimitive hsc (by norm_num) hprim).isMultiplyPretransitive

/-- In degree nine, a primitive permutation group containing a five-cycle contains A₉. -/
public theorem primitive_nine_alternating_le_of_five_dvd (U : Subgroup (Perm (Fin 9)))
    (hp : IsPreprimitive U (Fin 9)) (hfive : 5 ∣ Nat.card U) :
    alternatingGroup (Fin 9) ≤ U := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  have hgo : orderOf (g : Perm (Fin 9)) = 5 := by simpa using hg
  have hgc : (g : Perm (Fin 9)).IsCycle :=
    Perm.isCycle_of_prime_order' (hgo ▸ by decide) (by simp; omega)
  have := five_transitive_of_five_dvd U hp hfive
  obtain ⟨t, ht, ht3⟩ := threeCycle_of_five_transitive U g.property hgc hgo
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hp ht3 ht

/-- Five does not divide the order of a proper primitive subgroup of A₉. -/
public theorem primitive_nine_not_five_dvd_card
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : H ≠ ⊤)
    (hp : IsPreprimitive H (Fin 9)) : ¬ 5 ∣ Nat.card H := by
  intro hfive
  let i := (alternatingGroup (Fin 9)).subtype
  let U := H.map i
  let e : H ≃* U := H.equivMapOfInjective i (alternatingGroup (Fin 9)).subtype_injective
  let X : Fin 9 →ₑ[e.toMonoidHom] Fin 9 :=
    { toFun := id, map_smul' := fun _ _ => rfl }
  have hpU : IsPreprimitive U (Fin 9) :=
    (isPreprimitive_congr (f := X) e.surjective Function.bijective_id).mp hp
  have hle : alternatingGroup (Fin 9) ≤ U :=
    primitive_nine_alternating_le_of_five_dvd U hpU ((Nat.card_congr e.toEquiv) ▸ hfive)
  apply hH
  apply top_unique
  intro a _
  obtain ⟨b, hb, he⟩ := hle a.property
  exact ((alternatingGroup (Fin 9)).subtype_injective he) ▸ hb

end CFSG.Quasithin.MainConverse.NineReduction
