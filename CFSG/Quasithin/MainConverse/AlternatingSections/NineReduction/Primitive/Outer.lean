module

public import Theory.GroupAction.NinePointSevenCentralizer
public import Theory.GroupTheory.SmallIndexSolvable
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Sylow

/-!
# Solvable quotients from the seven-normalizer in degree nine

A seven-cycle on nine letters has centralizer of order fourteen. Its cyclic
subgroup has index two in that centralizer, so the centralizer is solvable.
Conjugation then proves that the normalizer of any subgroup of order seven
in a faithful degree-nine group is solvable.

If a normal subgroup has order divisible by seven, its Sylow seven-subgroups
have order seven because 7² does not divide 9!. Frattini's argument gives a
solvable normalizer supplement. The quotient is therefore solvable.

This supplies the outer-quotient clause of the primitive PSL₂(8) branch for
Aschbacher–Smith, Theorem 0.1.2(3), condition K, printed pp.4 and 482. It does
not require an automorphism classification or a list of primitive groups.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction
open Subgroup Equiv
open scoped IsMulCommutative

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem seven_cycle_centralizer_solvable (x : Perm (Fin 9)) (hx : orderOf x = 7) :
    Group.IsSolvable (centralizer ({x} : Set (Perm (Fin 9)))) := by
  let C := centralizer ({x} : Set (Perm (Fin 9)))
  have hC : Nat.card C = 14 := Perm.card_centralizer_order_seven_on_nine (by simp) x hx
  have hle : zpowers x ≤ C := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  let R := (zpowers x).subgroupOf C
  have hR : Nat.card R = 7 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hx]
  let : IsCyclic R := isCyclic_of_prime_card hR
  apply R.isSolvable_of_index_le_four
  have hm := R.card_mul_index
  rw [hR, hC] at hm
  omega

private theorem seven_subgroup_normalizer_solvable {H : Type*} [Group H]
    (i : H →* Perm (Fin 9)) (hi : Function.Injective i)
    (P : Subgroup H) (hP : Nat.card P = 7) :
    Group.IsSolvable (normalizer (P : Set H)) := by
  let : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := P)
  have hxo : orderOf (i x) = 7 := by
    rw [orderOf_injective i hi, Subgroup.orderOf_coe,
      orderOf_eq_card_of_forall_mem_zpowers hx, hP]
  let C := centralizer ({i x} : Set (Perm (Fin 9)))
  let : Group.IsSolvable C := seven_cycle_centralizer_solvable _ hxo
  let f : centralizer (P : Set H) →* C :=
    (i.comp (centralizer (P : Set H)).subtype).codRestrict C (by
      intro g
      apply mem_centralizer_singleton_iff.mpr
      change i g * i x = i x * i g
      simpa only [map_mul] using
        (congrArg i (mem_centralizer_iff.mp g.property x x.property)).symm)
  have hfi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (hi (congrArg Subtype.val hab))
  let : Group.IsSolvable (centralizer (P : Set H)) :=
    Group.isSolvable_of_isSolvable_injective hfi
  let e := subgroupOfEquivOfLe (centralizer_le_normalizer (P : Set H))
  let : Group.IsSolvable ((centralizer (P : Set H)).subgroupOf (normalizer (P : Set H))) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsSolvable P.normalizerMonoidHom.ker := by
    rw [P.normalizerMonoidHom_ker]
    infer_instance
  let : Group.IsSolvable (MulAut P) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (IsCyclic.mulAutMulEquiv P).toMonoidHom) (IsCyclic.mulAutMulEquiv P).injective
  exact Group.isSolvable_of_ker_le_range P.normalizerMonoidHom.ker.subtype
    P.normalizerMonoidHom (by simp)

/-- A normal subgroup with order divisible by seven has solvable quotient in any faithful degree-nine group. -/
public theorem quotient_solvable_of_seven_dvd {H : Type*} [Group H] [Finite H]
    (i : H →* Perm (Fin 9)) (hi : Function.Injective i)
    (N : Subgroup H) [N.Normal] (hseven : 7 ∣ Nat.card N) :
    Group.IsSolvable (H ⧸ N) := by
  let P : Sylow 7 N := Classical.choice inferInstance
  have hcard : Nat.card P = 7 := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hd : Nat.card P ∣ 362880 := by
      have hiP : Function.Injective (i.comp (N.subtype.comp P.toSubgroup.subtype)) :=
        hi.comp (N.subtype_injective.comp P.toSubgroup.subtype_injective)
      have hh := Subgroup.card_dvd_of_injective _ hiP
      simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using hh
    have hpos := P.dvd_card_of_dvd_card hseven
    rw [hk] at hd hpos ⊢
    have hkle : k ≤ 1 := by
      by_contra! h
      have h49 : 49 ∣ 362880 :=
        (Nat.pow_dvd_pow 7 (by omega : 2 ≤ k)).trans hd
      norm_num at h49
    interval_cases k <;> norm_num at *
  let Q := P.toSubgroup.map N.subtype
  have hQ : Nat.card Q = 7 :=
    (Nat.card_congr (P.toSubgroup.equivMapOfInjective N.subtype N.subtype_injective).toEquiv).symm.trans hcard
  let : Group.IsSolvable (normalizer (Q : Set H)) :=
    seven_subgroup_normalizer_solvable i hi Q hQ
  have hsup : normalizer (Q : Set H) ⊔ N = ⊤ := P.normalizer_sup_eq_top
  let q := QuotientGroup.mk' N
  let f : normalizer (Q : Set H) →* H ⧸ N := q.comp (normalizer (Q : Set H)).subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hg : g ∈ normalizer (Q : Set H) ⊔ N := by rw [hsup]; trivial
    obtain ⟨c, hc, n, hn, hcn⟩ := mem_sup_of_normal_right.mp hg
    refine ⟨⟨c,hc⟩, ?_⟩
    change q c = q g
    have hqn : q n = 1 := (QuotientGroup.eq_one_iff (N := N) n).mpr hn
    rw [← hcn, map_mul, hqn, mul_one]
  exact Group.isSolvable_of_surjective hf

end CFSG.Quasithin.MainConverse.NineReduction
