module

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.ActionBasics
public import BenderSuzuki.SE.Section11Lemma113Isaacs
public import Theory.AtlasPort.OtherSporadic.GroupTheory.CenterSimpleQuotient

/-!
# Seven-divisibility in the primitive degree-nine simple subgroup

The normal simple subgroup acts primitively by `ActionBasics`. If five
divides its order, Cauchy's theorem gives a five-cycle. Jordan's proved
multiple-primitivity criterion makes the action five-transitive, so seven
divides its order.

Otherwise, absence of seven would leave only the primes two and three in
the order, which divides nine factorial. A group of odd order with this
restriction is a three-group and has nontrivial center. In the even case,
choose an involution in the center of a Sylow two-subgroup. Its conjugacy
class has three-power size. The proved Isaacs 3.8–3.9 character argument
supplies a proper normal kernel modulo which this involution is central.
Simplicity makes the kernel trivial, contradicting the trivial center.

This is a recognition ingredient for condition K in the alternating case
of Aschbacher–Smith, `refs/quasithin.pdf`, printed pp.4 and 482. The proof
uses Jordan's multiple-primitivity theorem as formalized in Mathlib and
the involution form of Burnside's prime-power class argument proved in
`BenderSuzuki.SE.Section11Lemma113Isaacs`. Properness of the ambient
subgroup is unnecessary for this particular divisibility statement.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction

open MulAction Equiv Subgroup BenderSuzuki PFAppendixIII
open scoped Pointwise

/-- A five-cycle gives five-transitivity, whose orbit size contains a factor seven. -/
private theorem seven_dvd_card_of_five_dvd_card_primitive_nine (U : Subgroup (Perm (Fin 9)))
    (hp : IsPreprimitive U (Fin 9)) (hfive : 5 ∣ Nat.card U) :
    7 ∣ Nat.card U := by
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
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← hsupp]
    apply congr_arg Finset.card
    ext x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]
  have ht : IsMultiplyPretransitive U (Fin 9) 5 :=
    (hp.isMultiplyPreprimitive hsc (by norm_num) hprim).isMultiplyPretransitive
  let s : Set (Fin 9) := (↑({0, 1, 2, 3, 4} : Finset (Fin 9)))
  have hs : s.ncard = 5 := by
    change (↑({0, 1, 2, 3, 4} : Finset (Fin 9)) : Set (Fin 9)).ncard = 5
    rw [Set.ncard_coe_finset]
    decide
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq s (hs ▸ ht)
  have hd := (fixingSubgroup U s).index_dvd_card
  rw [hi, hs] at hd
  exact (by norm_num [Nat.choose, Nat.factorial] :
    7 ∣ Nat.choose (Nat.card (Fin 9)) 5 * Nat.factorial 5).trans hd

/-- Burnside's character kernel rules out a prime-power involution class in a simple group. -/
private theorem simple_involution_class_not_prime_power
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (t : G) (ht : IsInvolution t)
    (p k : ℕ) (hp : p.Prime)
    (hc : Nat.card (ConjClasses.mk t).carrier = p ^ k) : False := by
  classical
  let Z := (ConjClasses.mk t).carrier
  have hz (z : G) : z ∈ Z ↔ IsConj z t := by
    simp [Z, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  have hzconj (x y : G) (hx : x ∈ Z) (hy : y ∈ Z) :
      ∃ w : G, y = rightConjugateElem x w := by
    obtain ⟨w, hw⟩ := isConj_iff.mp (((hz x).mp hx).trans ((hz y).mp hy).symm)
    exact ⟨w⁻¹, by simpa [rightConjugateElem] using hw.symm⟩
  have htZ : t ∈ Z := (hz t).mpr (IsConj.refl t)
  obtain ⟨K, hKlt, hKn, hcentral⟩ := (is1_38_39 (⊤ : Subgroup G) Z p k hp
    ⟨t, htZ⟩ (by simp)
    (by
      intro z hz
      obtain ⟨w, rfl⟩ := hzconj t z htZ hz
      exact isInvolution_rightConjugateElem ht)
    (by
      intro z hzZ w _
      apply (hz _).mpr
      apply IsConj.trans ?_ ((hz z).mp hzZ)
      exact (isConj_iff.mpr ⟨w⁻¹, by simp [rightConjugateElem]⟩ :
        IsConj z (rightConjugateElem z w)).symm)
    (by
      intro x hx y hy
      obtain ⟨w, hw⟩ := hzconj x y hx hy
      exact ⟨w, trivial, hw⟩)
    hc).exists_H
  have hKn' : K.Normal := by
    rw [← normalizer_eq_top_iff]
    exact top_unique ((normal_subgroupOf_iff_le_normalizer le_top).mp hKn)
  have hK : K = ⊥ := hKn'.eq_bot_or_eq_top.resolve_right (ne_of_lt hKlt)
  have htcenter : t ∈ center G := by
    rw [mem_center_iff]
    intro g
    have h := hcentral t htZ g (by trivial)
    rw [hK, mem_bot] at h
    have hc : rightConjugateElem t g = t := mul_inv_eq_one.mp h
    dsimp [rightConjugateElem] at hc
    rw [mul_assoc] at hc
    exact (inv_mul_eq_iff_eq_mul.mp hc).symm
  rw [Atlas.GroupTheory.center_eq_bot_of_simple_nonabelian G hna, mem_bot] at htcenter
  exact ht.ne_one htcenter

/-- A nonabelian simple group cannot have only two and three as prime divisors. -/
private theorem simple_nonabelian_not_only_two_three
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3) : False := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htwo : 2 ∣ Nat.card G := by
    by_contra htwo
    have hn := Nat.eq_prime_pow_of_unique_prime_dvd (p := 3) Nat.card_pos.ne' (by
      intro q hq hqd
      exact (hprimes q hq hqd).resolve_left (by rintro rfl; exact htwo hqd))
    have hG : IsPGroup 3 G := IsPGroup.of_card hn
    have : Nontrivial (center G) := hG.center_nontrivial
    have hne : center G ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp this
    exact hne (Atlas.GroupTheory.center_eq_bot_of_simple_nonabelian G hna)
  let P : Sylow 2 G := Classical.choice inferInstance
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr (P.ne_bot_of_dvd_card htwo)
  have : Nontrivial (center P) := P.isPGroup'.center_nontrivial
  have hZtwo : 2 ∣ Nat.card (center P) :=
    (P.isPGroup'.to_subgroup (center P)).card_eq_or_dvd.resolve_left
      (Nat.ne_of_gt Finite.one_lt_card)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZtwo
  let t : G := (z : P)
  have htorder : orderOf t = 2 := by
    rw [show t = ((z : P) : G) from rfl, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have ht : IsInvolution t := by
    have h := orderOf_eq_prime_iff.mp htorder
    exact ⟨h.2, h.1⟩
  let C : Subgroup G := centralizer {t}
  have hPC : (P : Subgroup G) ≤ C := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((mem_center_iff.mp z.property) ⟨x, hx⟩)
  have hCtwo : ¬ 2 ∣ C.index := fun h =>
    P.not_dvd_index (h.trans (index_dvd_of_le hPC))
  have hk := Nat.eq_prime_pow_of_unique_prime_dvd (n := C.index) (p := 3)
    C.index_ne_zero_of_finite (by
      intro q hq hqd
      exact (hprimes q hq (hqd.trans C.index_dvd_card)).resolve_left
        (by rintro rfl; exact hCtwo hqd))
  have hc : Nat.card (ConjClasses.mk t).carrier = 3 ^ C.index.primeFactorsList.length := by
    rw [← hk]
    change Nat.card (ConjClasses.mk t).carrier = (centralizer {t}).index
    calc
      Nat.card (ConjClasses.mk t).carrier = (stabilizer (ConjAct G) t).index := by
        rw [index_stabilizer, ConjAct.orbit_eq_carrier_conjClasses]
        rfl
      _ = ((stabilizer (ConjAct G) t).comap ConjAct.toConjAct.toMonoidHom).index :=
        ((stabilizer (ConjAct G) t).index_comap_of_surjective
          (f := ConjAct.toConjAct.toMonoidHom) ConjAct.toConjAct.surjective).symm
      _ = (centralizer {t}).index :=
        congrArg Subgroup.index (centralizer_eq_comap_stabilizer t).symm
  exact simple_involution_class_not_prime_power hna t ht 3 _ Nat.prime_three hc

set_option linter.unusedVariables false in
/-- Seven divides the order of the nonabelian simple normal subgroup.
The properness hypothesis is retained for the recognition interface. -/
public theorem seven_dvd_card_primitive_simple_normal
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : H ≠ ⊤)
    (hp : IsPreprimitive H (Fin 9))
    (N : Subgroup H) [N.Normal] [IsSimpleGroup N]
    (hna : ¬ IsMulCommutative N) : 7 ∣ Nat.card N := by
  classical
  let f := toPermHom N (Fin 9)
  let e : N ≃* f.range := MonoidHom.ofInjective toPerm_injective
  let X : Fin 9 →ₑ[e.toMonoidHom] Fin 9 :=
    { toFun := id, map_smul' := fun _ _ => rfl }
  have hpU : IsPreprimitive f.range (Fin 9) :=
    (isPreprimitive_congr (f := X) e.surjective Function.bijective_id).mp
      (primitive_simple_normal_preprimitive H hp N)
  have hcard : Nat.card N ∣ Nat.factorial 9 := by
    have hd := Subgroup.card_dvd_of_injective f (show Function.Injective f from toPerm_injective)
    rw [Nat.card_perm, Nat.card_fin] at hd
    exact hd
  by_contra hseven
  have hfive : ¬ 5 ∣ Nat.card N := by
    intro hfive
    have hU := seven_dvd_card_of_five_dvd_card_primitive_nine f.range hpU
      ((Nat.card_congr e.toEquiv) ▸ hfive)
    exact hseven ((Nat.card_congr e.toEquiv).symm ▸ hU)
  apply simple_nonabelian_not_only_two_three hna
  intro p hprime hpd
  have hp9 : p ≤ 9 := hprime.dvd_factorial.mp (hpd.trans hcard)
  interval_cases p <;> (try norm_num at hprime) <;> (try norm_num)
  · exact False.elim (hfive hpd)
  · exact False.elim (hseven hpd)

end CFSG.Quasithin.MainConverse.NineReduction
