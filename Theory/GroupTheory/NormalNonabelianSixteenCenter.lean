module
public import Theory.GroupTheory.NormalSixteenCommutativity
public import Theory.GroupAction.FixedIndexTwoResidual
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Centers of normal nonabelian subgroups of order sixteen

The center has order two or four. At order four the central quotient is a
four-group, and the derived subgroup is a characteristic central subgroup
of order two. Hence in either case there is a characteristic involution.
Its ambient image is central. The action on the core center fixes a subgroup
of index at most two, so every two-perfect actor acts trivially.

If the core is self-centralizing, the center of any ambient Sylow two-subgroup
lies in the core center. Both the two-residual and that Sylow centralize it,
and together they generate the ambient group.

Source application: Aschbacher–Smith F.1.12(I)(8), F.6.5 (pp.263,305).
This elementary order-sixteen argument avoids a classification of small groups.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace NormalNonabelianSixteen
private theorem quotient_is_klein_four {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card (H ⧸ Subgroup.center H) = 4)
    (hncyc : ¬ IsCyclic (H ⧸ Subgroup.center H)) :
    IsKleinFour (H ⧸ Subgroup.center H) := by
  let _ : Nontrivial (H ⧸ Subgroup.center H) :=
    (Finite.one_lt_card_iff_nontrivial).mp (by rw [hcard]; omega)
  refine ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr ?_⟩
  intro x hx
  have hxdvd : orderOf x ∣ 4 := by
    rw [← hcard]
    exact orderOf_dvd_natCard x
  have hxone : orderOf x ≠ 1 := by simpa using hx
  have hxnotfour : orderOf x ≠ 4 := by
    intro hfour
    exact hncyc (isCyclic_of_orderOf_eq_card x (hfour.trans hcard.symm))
  obtain ⟨k, hk, hpow⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf x ∣ 2 ^ 2 by simpa using hxdvd)
  interval_cases k
  · exact (hxone hpow).elim
  · exact hpow
  · exact (hxnotfour hpow).elim


private theorem center_index_ge_four {H : Type*} [Group H] [Finite H]
    (hn : ¬ IsMulCommutative H) : 4≤(center H).index := by
  by_contra! hi
  have he := center_eq_and_index_four_of_central_small_index (center H) le_rfl
    (by omega) ((commutator_eq_bot_iff H).not.mpr hn)
  omega

private theorem derived_card_two {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H=16) (hcenterCard : 4≤Nat.card (center H))
    (hcomm : ¬ IsMulCommutative H) :
    Nat.card (_root_.commutator H)=2 ∧ _root_.commutator H≤center H := by
  have hderived : _root_.commutator H ≠ ⊥ := (commutator_eq_bot_iff H).not.mpr hcomm
  have hindex : (Subgroup.center H).index ≤ 4 := by
    have hprod := (Subgroup.center H).card_mul_index
    rw [hcard] at hprod
    have hdiv := (Subgroup.center H).card_subgroup_dvd_card
    rw [hcard] at hdiv
    have hcenterle : Nat.card (Subgroup.center H) ≤ 16 :=
      Nat.le_of_dvd (by omega) hdiv
    nlinarith
  have hcenterEq := Subgroup.center_eq_and_index_four_of_central_small_index
    (Subgroup.center H) le_rfl hindex hderived
  have hquotCard : Nat.card (H ⧸ Subgroup.center H) = 4 := by
    rw [← (Subgroup.center H).index_eq_card, hcenterEq.2]
  let Q := H ⧸ Subgroup.center H
  let _ : IsKleinFour Q := quotient_is_klein_four hquotCard (fun hcyc =>
    hcomm (isMulCommutative_of_isCyclic_quotient_center_self H))
  let e : Q ≃* DihedralGroup 2 := IsKleinFour.nonempty_mulEquiv.some
  let f : H →* DihedralGroup 2 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center H))
  have hker : f.ker ≤ Subgroup.center H := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    change e (QuotientGroup.mk' (Subgroup.center H) x) = 1 at hx
    exact e.injective (hx.trans e.map_one.symm)
  have hbound := CentralExtension.card_center_inf_commutator_le_two_of_dihedral f hf hker
  have hcommCenter : _root_.commutator H ≤ Subgroup.center H := by
    change ⁅(⊤ : Subgroup H), ⊤⁆ ≤ Subgroup.center H
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (Subgroup.center H)) ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    have hc := ((commutator_eq_bot_iff Q).mpr IsKleinFour.isMulCommutative :
      _root_.commutator Q = ⊥)
    have hm : ⁅(QuotientGroup.mk' (Subgroup.center H)) x,
        (QuotientGroup.mk' (Subgroup.center H)) y⁆ ∈ _root_.commutator Q :=
      Subgroup.commutator_mem_commutator trivial trivial
    rw [hc] at hm
    exact hm
  have hcommCard : Nat.card (_root_.commutator H) ≤ 2 := by
    rw [inf_eq_right.mpr hcommCenter] at hbound
    exact hbound
  have hcommCardEq : Nat.card (_root_.commutator H) = 2 := by
    have hnontriv : Nat.card (_root_.commutator H) ≠ 1 := by
      intro hone
      exact hderived (Subgroup.card_eq_one.mp hone)
    have hpos := Nat.card_pos (α := _root_.commutator H)
    omega
  exact ⟨hcommCardEq,hcommCenter⟩

/-- A nonabelian group of order sixteen has a characteristic central involution. -/
theorem exists_characteristic_two {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H=16) (hn : ¬ IsMulCommutative H) :
    ∃ K : Subgroup H, K.Characteristic ∧ Nat.card K=2 ∧ K≤center H := by
  have hp : IsPGroup 2 H := IsPGroup.of_card (n:=4) (by simpa using hcard)
  let : Nontrivial H := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  have hzpos : 1<Nat.card (center H) := by
    let := hp.center_nontrivial
    exact Finite.one_lt_card
  have hh := (center H).card_mul_index
  have hi := center_index_ge_four hn
  rw [hcard] at hh
  have hzle : Nat.card (center H)≤4 := by nlinarith
  have hd : Nat.card (center H)∣16 := hcard ▸ (center H).card_subgroup_dvd_card
  have hc : Nat.card (center H)=2 ∨ Nat.card (center H)=4 := by
    interval_cases hc : Nat.card (center H) <;> norm_num at *
  rcases hc with hc | hc
  · exact ⟨center H,inferInstance,hc,le_rfl⟩
  · have hh := derived_card_two hcard (by omega) hn
    exact ⟨_root_.commutator H,inferInstance,hh.1,hh.2⟩

/-- A two-residual centralizes the center of a normal nonabelian sixteen. -/
theorem pResidual_centralizes_center
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G) [Q.Normal]
    (hQ : Nat.card Q=16) (hn : ¬ IsMulCommutative Q) :
    pResidual 2 G≤centralizer ((center Q).map Q.subtype : Set G) := by
  obtain ⟨K,hK,hKc,hKZ⟩ := exists_characteristic_two hQ hn
  let := hK
  let Z := (center Q).map Q.subtype
  let D := K.map Q.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  let : D.Normal := ConjAct.normal_of_characteristic_of_normal
  have hDc : Nat.card D=2 := (card_map_of_injective Q.subtype_injective).trans hKc
  have hDZ : D≤Z := map_mono hKZ
  have hDcentral : D≤center G := central_of_normal_card_two D hDc
  let ρ : pResidual 2 G →* MulAut Z :=
    (MulAut.conjNormal : G→*MulAut Z).comp (pResidual 2 G).subtype
  have hZcard : Nat.card Z≤4 := by
    rw [card_map_of_injective Q.subtype_injective]
    have hi := center_index_ge_four hn
    have hh := (center Q).card_mul_index
    rw [hQ] at hh
    nlinarith
  have hidx : (D.subgroupOf Z).index≤2 := by
    have hh := (D.subgroupOf Z).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hDZ).toEquiv,hDc] at hh
    omega
  have hp : IsPGroup 2 Z := ((IsPGroup.of_card (n:=4) (by simpa using hQ)).to_subgroup
    (center Q)).map Q.subtype
  have ht (a : pResidual 2 G) : ρ a=1 :=
    MulAut.eq_one_of_pPerfect_of_fixed_index_le_two ρ (isPPerfect_pResidual 2) hp
      (D.subgroupOf Z) hidx (by
        intro a x hx
        apply Subtype.ext
        change (a:G)*(x:G)*(a:G)⁻¹=(x:G)
        exact mul_inv_eq_iff_eq_mul.mpr ((mem_center_iff.mp (hDcentral hx)) a)) a
  intro a ha
  rw [mem_centralizer_iff]
  intro z hz
  have he := congrArg (fun f : MulAut Z => (f ⟨z,hz⟩ : G)) (ht ⟨a,ha⟩)
  change a*z*a⁻¹=z at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
/-- In characteristic two, the center of an ambient Sylow centralizes the
whole vertex when its normal two-core is a nonabelian sixteen. -/
theorem sylow_center_le_center
    {G : Type*} [Group G] [Finite G] (Q : Subgroup G) [Q.Normal]
    (hQ : Nat.card Q=16) (hn : ¬ IsMulCommutative Q)
    (hc : centralizer (Q : Set G)≤Q) (S : Sylow 2 G) :
    (center (S : Subgroup G)).map (S : Subgroup G).subtype≤center G := by
  let Z := (center (S : Subgroup G)).map (S : Subgroup G).subtype
  have hQS : Q≤(S : Subgroup G) :=
    (IsPGroup.of_card (n:=4) (by simpa using hQ)).le_sylow_of_normal S
  have hZC : Z≤centralizer (S : Set G) := by
    rintro _ ⟨z,hz,rfl⟩
    rw [mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨t,ht⟩)
  have hZQ : Z≤(center Q).map Q.subtype := by
    intro z hz
    have hqc : z∈centralizer (Q : Set G) := (centralizer_le hQS) (hZC hz)
    have hzq := hc hqc
    refine ⟨⟨z,hzq⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext (mem_centralizer_iff.mp hqc q q.property)
  have hr : pResidual 2 G≤centralizer (Z : Set G) :=
    (pResidual_centralizes_center Q hQ hn).trans (centralizer_le hZQ)
  have hall : (⊤ : Subgroup G)≤centralizer (Z : Set G) := by
    rw [←pResidual_sup_sylow_eq_top S]
    exact sup_le hr (le_centralizer_iff.mp hZC)
  exact centralizer_eq_top_iff_subset.mp (top_unique hall)
end NormalNonabelianSixteen

