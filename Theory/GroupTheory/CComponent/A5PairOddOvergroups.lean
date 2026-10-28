module
public import Theory.GroupTheory.SimplePairPrimeSupport
public import Theory.GroupTheory.CComponent.A5PairSylowMaximal

/-!
# Odd subgroups in proper overgroups of an exchanged A₅ pair

Modulo the ambient two-core, an A₅ C-component with normalizer index two
has a disjoint commuting conjugate. A proper overgroup of the given Sylow
two-subgroup projects into the order-twelve Borel subgroup in each factor.
It is consequently a {2,3}-group. This conclusion lifts through the full
two-core, and its odd-order subgroups are three-groups.

Source application: Aschbacher–Smith, The Classification of Quasithin Groups,
10.2.3, printed pp.744–745. No action-faithfulness assertion is made here.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.Alternating.FiveSylowMaximal
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem five_sylow_normalizer_six
    (S : Sylow 2 (alternatingGroup (Fin 5))) :
    IsPGroup 6 (normalizer (S : Set (alternatingGroup (Fin 5)))) := by
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer S
  rw [hi]
  have hc : Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by
    rw [Nat.card_eq_fintype_card]
    clear hi S
    revert i
    decide +kernel
  exact IsPGroup.of_card_dvd_pow (n := 2) (by rw [hc]; decide)

private theorem five_overgroup_six
    (S : Sylow 2 G) (e : G ≃* alternatingGroup (Fin 5))
    (P : Subgroup G) (hSP : (S : Subgroup G) ≤ P) (hP : P ≠ ⊤) : IsPGroup 6 P := by
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP' : P.map e.toMonoidHom ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.comap e.toMonoidHom) he
    rw [comap_map_eq_self_of_injective e.injective, comap_top] at hh
    exact hP hh
  have hle := overgroup_le_sylow_normalizer S' (P.map e.toMonoidHom) (map_mono hSP) hP'
  exact ((five_sylow_normalizer_six S').to_le hle).of_equiv
    (P.equivMapOfInjective e.toMonoidHom e.injective).symm

private theorem five_intersection_overgroup_six
    (S : Sylow 2 G) (A : Subgroup G) (hs : A.IsSubnormal)
    (e : A ≃* alternatingGroup (Fin 5))
    (P : Subgroup G) (hSP : A ⊓ (S : Subgroup G) ≤ P) (hP : P < A) :
    IsPGroup 6 P := by
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_subnormal A hs
  have hle : (R : Subgroup A) ≤ P.subgroupOf A := by
    rw [hR]
    intro a ha
    exact hSP ⟨a.property, ha⟩
  have hne : P.subgroupOf A ≠ ⊤ := fun he => hP.not_ge (subgroupOf_eq_top.mp he)
  exact (five_overgroup_six R e (P.subgroupOf A) hle hne).of_equiv
    (subgroupOfEquivOfLe hP.le)

private theorem five_sylow_intersection (S : Sylow 2 G) (A : Subgroup G)
    (hs : A.IsSubnormal) (e : A ≃* alternatingGroup (Fin 5)) :
    Order.HasUniqueMaximalOver (A ⊓ (S : Subgroup G)) A ∧ A ⊓ (S : Subgroup G) ≠ ⊥ := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hs
  have hu : Order.HasUniqueMaximalOver (P : Subgroup A) ⊤ :=
    hasUniqueMaximalOver_of_surjective e.toMonoidHom e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact bot_le)
      (sylow_unique (P.mapSurjective e.surjective))
  have hum := hasUniqueMaximalOver_map_subtype hu
  rw [hP, subgroupOf_map_subtype, inf_comm] at hum
  refine ⟨hum, ?_⟩
  have hd : 2 ∣ Nat.card A := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  intro he
  apply P.ne_bot_of_dvd_card hd
  apply (map_eq_bot_iff_of_injective _ A.subtype_injective).mp
  rw [hP, subgroupOf_map_subtype, inf_comm]
  exact he

private theorem five_simple_pair_proper_six (S : Sylow 2 G) (A : Subgroup G)
    (hA : A.IsCComponent) (e : A ≃* alternatingGroup (Fin 5))
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤)
    (V : Subgroup G) (hSV : (S : Subgroup G) ≤ V) (hV : V ≠ ⊤) :
    IsPGroup 6 V := by
  have hs : ¬ (S : Subgroup G) ≤ normalizer (A : Set G) := by
    intro hs
    have hd := index_dvd_of_le hs
    rw [hi] at hd
    exact S.not_dvd_index hd
  obtain ⟨s,hs,hsn⟩ := Set.not_subset.mp hs
  let B := A.map (MulAut.conj s).toMonoidHom
  have hm : B ≠ A := fun he => hsn (mem_normalizer_iff_map_conj_eq.mpr he)
  have hB : B.IsCComponent := hA.map_equiv (MulAut.conj s)
  let eB : B ≃* alternatingGroup (Fin 5) := ((MulAut.conj s).subgroupMap A).symm.trans e
  let : IsSimpleGroup A := e.isSimpleGroup
  let : IsSimpleGroup B := eB.isSimpleGroup
  let := hA.perfect
  have hc : B ≤ centralizer (A : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]
      exact simple_subnormal_commute_of_ne A B hA.subnormal hB.subnormal hm.symm)
  obtain ⟨huA,hneA⟩ := five_sylow_intersection S A hA.subnormal e
  obtain ⟨huB,hneB⟩ := five_sylow_intersection S B hB.subnormal eB
  have htop : (A ⊔ B) ⊔ (S : Subgroup G) = ⊤ :=
    top_unique (hgen ▸ sup_le_sup (le_sup_left : A ≤ A ⊔ B) le_rfl)
  exact isPGroup_of_simple_pair_proper_overgroup 6 A B (S : Subgroup G) V hc
    huA huB hneA hneB
    (conjugate_pair_permutation A B (S : Subgroup G) hm.symm
      (fun g _ => NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm g) s hs rfl)
    ⟨s,hs,rfl⟩ (five_intersection_overgroup_six S A hA.subnormal e)
    (five_intersection_overgroup_six S B hB.subnormal eB)
    (S.isPGroup'.mono (by decide : 2 ∣ 6)) hSV (htop ▸ lt_top_iff_ne_top.mpr hV)

/-- A proper Sylow overgroup in the exchanged A₅ pair has only prime
divisors two and three, including its full two-core. -/
theorem IsCComponent.a5_pair_proper_overgroup_six
    (S : Sylow 2 G) (A : Subgroup G) (hA : A.IsCComponent)
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤)
    (V : Subgroup G) (hSV : (S : Subgroup G) ≤ V) (hV : V ≠ ⊤) :
    IsPGroup 6 V := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let q := QuotientGroup.mk' (pCore 2 G)
  let Abar := A.map q
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hAb : Abar.IsCComponent := hA.map_quotient (pCore 2 G)
  let eb : Abar ≃* alternatingGroup (Fin 5) := (cComponentTwoCoreQuotientEquiv hA).symm.trans e
  have hib : (normalizer (Abar : Set (G ⧸ pCore 2 G))).index = 2 :=
    (cComponent_normalizer_index_quotient hA (pCore 2 G)).trans hi
  have hgenb : Abar ⊔ (Sbar : Subgroup (G ⧸ pCore 2 G)) = ⊤ := by
    change A.map q ⊔ (S : Subgroup G).map q = ⊤
    rw [← map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hk : q.ker ≤ V := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSV
  have hVb : V.map q ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.comap q) he
    rw [comap_map_eq_self hk, comap_top] at hh
    exact hV hh
  have h6 := five_simple_pair_proper_six Sbar Abar hAb eb hib hgenb
    (V.map q) (map_mono hSV) hVb
  have hk6 : IsPGroup 6 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.mono (by decide : 2 ∣ 6)
  have h := h6.comap_of_ker_isPGroup q hk6
  rwa [comap_map_eq_self hk] at h

/-- Every odd-order subgroup of a proper Sylow overgroup in the exchanged
A₅ pair is a three-group. -/
theorem IsCComponent.a5_pair_odd_subgroup_isThreeGroup
    (S : Sylow 2 G) (A : Subgroup G) (hA : A.IsCComponent)
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤)
    (V B : Subgroup G) (hSV : (S : Subgroup G) ≤ V) (hV : V ≠ ⊤)
    (hBV : B ≤ V) (hBodd : Odd (Nat.card B)) : IsPGroup 3 B := by
  have h6 := (hA.a5_pair_proper_overgroup_six S A e hi hgen V hSV hV).to_le hBV
  obtain ⟨n, hn⟩ := h6.exists_card_dvd_pow
  have hn' : Nat.card B ∣ 2 ^ n * 3 ^ n := by simpa only [← mul_pow, show 2 * 3 = 6 by decide] using hn
  exact IsPGroup.of_card_dvd_pow ((hBodd.coprime_two_right.pow_right n).dvd_of_dvd_mul_left hn')

end Subgroup
