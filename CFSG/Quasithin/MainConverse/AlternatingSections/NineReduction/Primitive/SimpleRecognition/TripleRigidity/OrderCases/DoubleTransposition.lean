module

public import Mathlib.GroupTheory.GroupAction.Jordan

/-!
# Double transpositions in a triple-transitive degree-nine action

Normalize a double transposition to `(0 1)(2 3)`. The setwise stabilizer of
`{0,1}` acts transitively on its seven-point complement and contains a
transposition in this action. A transitive prime-degree action is primitive,
so Jordan's transposition theorem makes the image S₇. Its order is divisible
by five, and hence so is the original group's order.

Combined with `FiveExclusion`, this excludes double transpositions from the
proper primitive overgroup used in degree-nine recognition. Application:
Aschbacher–Smith, *The Classification of Quasithin Groups*, `refs/quasithin.pdf`,
condition K and the alternating case, printed pp.4 and 482.
-/

open Equiv Equiv.Perm MulAction Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.MainConverse.NineReduction

private def doubleSwap : Perm (Fin 9) := swap 0 1 * swap 2 3
private abbrev pairComplement : Set (Fin 9) := {0, 1}ᶜ

private theorem normalized_five_dvd (U : Subgroup (Perm (Fin 9)))
    [IsMultiplyPretransitive U (Fin 9) 3] (hg : doubleSwap ∈ U) : 5 ∣ Nat.card U := by
  classical
  let S := stabilizer U pairComplement
  let f := toPermHom S pairComplement
  let V := f.range
  have htrans : IsPretransitive V pairComplement := by
    constructor
    intro x y
    let ex : Fin 3 ↪ Fin 9 := ⟨![0, 1, x.val], by
      have hx : x.val ≠ 0 ∧ x.val ≠ 1 := by simpa only [pairComplement, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using x.property
      simp only [Function.Injective]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
    let ey : Fin 3 ↪ Fin 9 := ⟨![0, 1, y.val], by
      have hy : y.val ≠ 0 ∧ y.val ≠ 1 := by simpa only [pairComplement, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using y.property
      simp only [Function.Injective]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
    obtain ⟨k, hk⟩ := exists_smul_eq U ex ey
    have hk0 : (k : Perm (Fin 9)) 0 = 0 := congrArg (fun e : Fin 3 ↪ Fin 9 => e 0) hk
    have hk1 : (k : Perm (Fin 9)) 1 = 1 := congrArg (fun e : Fin 3 ↪ Fin 9 => e 1) hk
    have hkx : (k : Perm (Fin 9)) x.val = y.val := congrArg (fun e : Fin 3 ↪ Fin 9 => e 2) hk
    have hkS : k ∈ S := by
      change k ∈ stabilizer U ({0, 1} : Set (Fin 9))ᶜ
      rw [stabilizer_compl, mem_stabilizer_iff]
      simp only [Set.smul_set_insert, Set.smul_set_singleton]
      change {((k : Perm (Fin 9)) 0), ((k : Perm (Fin 9)) 1)} = _
      rw [hk0, hk1]
    exact ⟨⟨f ⟨k, hkS⟩, ⟨⟨k, hkS⟩, rfl⟩⟩, Subtype.ext hkx⟩
  have hc : Nat.card pairComplement = 7 := by
    change ({0, 1}ᶜ : Set (Fin 9)).ncard = 7
    have h := Set.ncard_add_ncard_compl ({0, 1} : Set (Fin 9))
    norm_num at h ⊢
    omega
  have hp : IsPreprimitive V pairComplement := IsPreprimitive.of_prime_card (hc ▸ Nat.prime_seven)
  have hgS : (⟨doubleSwap, hg⟩ : U) ∈ S := by
    change (⟨doubleSwap, hg⟩ : U) ∈ stabilizer U ({0, 1} : Set (Fin 9))ᶜ
    rw [stabilizer_compl, mem_stabilizer_iff]
    change doubleSwap '' ({0, 1} : Set (Fin 9)) = {0, 1}
    simp [Set.image_insert_eq, Set.image_singleton, doubleSwap, Equiv.swap_apply_def, Set.pair_comm]
  let t : S := ⟨⟨doubleSwap, hg⟩, hgS⟩
  have ht : (f t).IsSwap := by
    refine ⟨⟨2, by simp [pairComplement]⟩, ⟨3, by simp [pairComplement]⟩, by decide, ?_⟩
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change doubleSwap x.val = _
    rcases x with ⟨x, hx⟩
    change ¬ (x = 0 ∨ x = 1) at hx
    fin_cases x <;> simp_all [pairComplement, doubleSwap, Equiv.swap_apply_def]
    all_goals exact hx (by decide)
  have hV : V = ⊤ := subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hp (f t) ht ⟨t, rfl⟩
  have hf : Function.Surjective f := (MonoidHom.range_eq_top).mp hV
  have hd := Subgroup.card_dvd_of_surjective f hf
  rw [Nat.card_perm, hc] at hd
  exact (by decide : 5 ∣ Nat.factorial 7).trans (hd.trans S.card_subgroup_dvd_card)

/-- A triple-transitive degree-nine group containing a double transposition has order divisible by five. -/
public theorem nine_five_dvd_of_three_transitive_double_transposition (U : Subgroup (Perm (Fin 9)))
    (hthree : IsMultiplyPretransitive U (Fin 9) 3)
    {g : Perm (Fin 9)} (hg : g ∈ U) (hc : g.cycleType = {2, 2}) : 5 ∣ Nat.card U := by
  classical
  have hconj : IsConj g doubleSwap := isConj_iff_cycleType_eq.mpr (by
    rw [hc]
    exact (show doubleSwap.cycleType = {2, 2} by decide +kernel).symm)
  obtain ⟨e, he⟩ := isConj_iff.mp hconj
  let V := U.map (MulAut.conj e).toMonoidHom
  let E : U ≃* V := U.equivMapOfInjective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective
  let X : Fin 9 →ₑ[E.toMonoidHom] Fin 9 :=
    { toFun := e, map_smul' := by
        intro u x
        change e ((u : Perm (Fin 9)) x) = (e * (u : Perm (Fin 9)) * e⁻¹) (e x)
        simp }
  have htV : IsMultiplyPretransitive V (Fin 9) 3 :=
    (IsPretransitive.of_embedding_congr (n := Fin 3) (f := X) E.surjective e.bijective).mp hthree
  have hgV : doubleSwap ∈ V := Subgroup.mem_map.mpr ⟨g, hg, he⟩
  have hd := normalized_five_dvd V hgV
  exact (Nat.card_congr E.toEquiv).symm ▸ hd

end CFSG.Quasithin.MainConverse.NineReduction
