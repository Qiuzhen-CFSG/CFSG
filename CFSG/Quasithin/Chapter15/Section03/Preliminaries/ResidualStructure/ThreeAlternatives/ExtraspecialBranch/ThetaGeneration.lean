module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.ExtraspecialBranch.Faithfulness
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Theta generation in the extraspecial branch of 15.3.7

Let Y be the literal residual O²(⟨Rcᴹ⟩), and P its image in M/O₂(M).
The preceding faithful-action argument makes every three-subgroup of
C_M(V)* cyclic. Adjoining a cubic element of this centralizer to Z(P)
therefore places it in Z(P), the unique subgroup of order three in that
cyclic overgroup. The actual residual action image then writes every cubic
element of M* as a product of an element of P and a commuting cubic kernel
element. Thus every order-three generator of θ(M) lies in Y O₂(M), and
normality of Y in M removes the two-group quotient, giving θ(M) ≤ Y.

Conversely, the Heisenberg model gives exponent three in Y/O₂(Y).
Prime-regular lifting supplies order-three representatives, so
Y = θ(Y) O₂(Y). Two-perfectness of Y removes this last two-group quotient
and proves Y ≤ θ(M). Only relative normality in M or Y is used.
The cardinality premise |P| = 27 is redundant once its actual Heisenberg
isomorphism is supplied; neither Rc-image cyclicity nor theta generation
is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 15.3.7,
printed p.1122 (PDF p.1139). The lifting step uses the same elementary
prime-regular argument as the later Section 15.3 FactorGeneration.Theta
module, without importing that downstream assembly.
-/

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives.ExtraspecialBranch
variable {G : Type*} [Group G] [Finite G]
variable {M Mc V : Subgroup G} {T : Sylow 2 G} {d : NaturalOrthogonalAction M V}

private theorem cyclic_mem_of_pow_card_eq_one {H : Type*} [Group H] [Finite H]
    [IsCyclic H] (A : Subgroup H) {x : H} (hx : x ^ Nat.card A = 1) : x ∈ A := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have hsub : (A : Set H).toFinset ⊆ Finset.univ.filter (fun a : H => a ^ Nat.card A = 1) := by
    intro a ha
    simp only [Set.mem_toFinset] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : A)))
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    simpa [Set.toFinset_card, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      using IsCyclic.card_pow_eq_one_le (α := H) (Nat.card_pos (α := A)))
  apply Set.mem_toFinset.mp
  rw [heq]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩

private theorem star_centralizer_cubic_mem_center (h : SourceInputs M Mc V T d)
    [IsExtraspecial 3 (star M (residualY M Mc))]
    (x : StarGroup M) (hx : x ∈ (starActor d h.core_le_kernel).ker) (hx3 : x ^ 3 = 1) :
    x ∈ (center (star M (residualY M Mc))).map (star M (residualY M Mc)).subtype := by
  let P := star M (residualY M Mc)
  let Z := (center P).map P.subtype
  let A := Z ⊔ zpowers x
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hp : IsPGroup 3 P := IsExtraspecial.isPGroup 3 P
  have hZp : IsPGroup 3 Z := (hp.to_subgroup (center P)).map P.subtype
  have hxp : IsPGroup 3 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hx3)
  have hZC : Z ≤ (starActor d h.core_le_kernel).ker := by
    rintro _ ⟨z, hz, rfl⟩
    change z ∈ ((starActor d h.core_le_kernel).domRestrict P).ker
    rwa [star_residual_actor_ker h]
  have hAC : A ≤ star M (M ⊓ centralizer (V : Set G)) := by
    rw [← ker_starActor d h.core_le_kernel]
    exact sup_le hZC (zpowers_le.mpr hx)
  let : IsCyclic A := star_centralizer_three_subgroups_cyclic h hp A
    (hZp.to_sup_of_normal_left hxp) hAC
  have hZA : Z ≤ A := le_sup_left
  have hc : Nat.card (Z.subgroupOf A) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv,
      card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 3 P
  exact cyclic_mem_of_pow_card_eq_one (Z.subgroupOf A)
    (x := ⟨x, (show zpowers x ≤ A from le_sup_right) (mem_zpowers x)⟩)
    (by rw [hc]; exact Subtype.ext hx3)

omit [Finite G] in
private theorem star_cube_eq_one
    (he : Nonempty (star M (residualY M Mc) ≃* HeisenbergPrime 3))
    (x : star M (residualY M Mc)) : x ^ 3 = 1 := by
  obtain ⟨e⟩ := he
  apply e.injective
  rw [map_pow, HeisenbergPrime.pow_prime (by decide), map_one]

private theorem twoResidualAmbient_eq_map_pResidual (H : Subgroup G) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 2
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    refine ⟨hN, ?_⟩
    let := hN
    exact IsPGroup.iff_card.mpr ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  · rintro ⟨hN, hp⟩
    let := hN
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    exact ⟨hN, n, by simpa [Subgroup.index_eq_card] using hn⟩

private theorem star_cubic_mem_residual (h : SourceInputs M Mc V T d)
    [IsExtraspecial 3 (star M (residualY M Mc))]
    (he : Nonempty (star M (residualY M Mc) ≃* HeisenbergPrime 3))
    (x : StarGroup M) (hx3 : x ^ 3 = 1) : x ∈ star M (residualY M Mc) := by
  let P := star M (residualY M Mc)
  let f := starActor d h.core_le_kernel
  have hf3 : f x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hfmem : f x ∈ P.map f := by
    rw [map_starActor, h.residual_image, twoResidualAmbient_eq_map_pResidual]
    let a : (⊤ : Subgroup OrthogonalActor) := ⟨f x, trivial⟩
    refine ⟨a, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
    exact (by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one (show a ^ 3 = 1 from Subtype.ext hf3))
  obtain ⟨y, hy, hyf⟩ := hfmem
  let k := y⁻¹ * x
  have hk : k ∈ f.ker := by
    change f (y⁻¹ * x) = 1
    rw [map_mul, map_inv, hyf, inv_mul_cancel]
  have hcomm : Commute y k :=
    mem_centralizer_iff.mp (starActor_ker_le_centralizer h hk) y hy
  have hy3 : y ^ 3 = 1 := congrArg Subtype.val (star_cube_eq_one he ⟨y, hy⟩)
  have hk3 : k ^ 3 = 1 := by
    have heq : (y * k) ^ 3 = 1 := by simpa [k] using hx3
    rwa [hcomm.mul_pow, hy3, one_mul] at heq
  have hkP : k ∈ P := map_subtype_le _ (star_centralizer_cubic_mem_center h k hk hk3)
  simpa [k] using P.mul_mem hy hkP

private theorem theta_le_residual (h : SourceInputs M Mc V T d)
    [IsExtraspecial 3 (star M (residualY M Mc))]
    (he : Nonempty (star M (residualY M Mc) ≃* HeisenbergPrime 3)) :
    theta M ≤ residualY M Mc := by
  let N := (residualY M Mc).subgroupOf M
  let : N.Normal := residualY_normal M Mc
  let Q := pCore 2 M
  let q := QuotientGroup.mk' Q
  let π := QuotientGroup.mk' N
  apply (closure_le _).mpr
  rintro x ⟨hxM, hxo⟩
  let a : M := ⟨x, hxM⟩
  have ha3 : a ^ 3 = 1 := Subtype.ext (hxo ▸ pow_orderOf_eq_one x)
  have hs : q a ∈ N.map q := star_cubic_mem_residual h he (q a)
    (by rw [← map_pow, ha3, map_one])
  have ha : a ∈ N ⊔ Q := by
    have hm : a ∈ (N.map q).comap q := hs
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk'] using hm
  have hb : π a ∈ Q.map π := by
    have hm := mem_map_of_mem π ha
    simpa only [Subgroup.map_sup, π, QuotientGroup.map_mk'_self, bot_sup_eq] using hm
  let b : Q.map π := ⟨π a, hb⟩
  have hb3 : b ^ 3 = 1 := Subtype.ext (by
    change π a ^ 3 = 1
    rw [← map_pow, ha3, map_one])
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := M)).map π b
  have hb1 : b = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow_left k)
      (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hb3))
  exact (QuotientGroup.eq_one_iff a).mp (congrArg Subtype.val hb1)

private theorem residual_le_theta
    (he : Nonempty (star M (residualY M Mc) ≃* HeisenbergPrime 3)) :
    residualY M Mc ≤ theta M := by
  let Y := residualY M Mc
  let N := (theta Y).subgroupOf Y
  let Q := pCore 2 Y
  let q := QuotientGroup.mk' Q
  let e := residualCoreQuotientEquivStar M Mc
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer (theta_le Y)).mpr
    (Y.le_normalizer.trans (normalizer_le_normalizer_theta Y))
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hcube (z : Y ⧸ Q) : z ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, star_cube_eq_one he, map_one]
  have hm : N.map q = ⊤ := by
    apply top_unique
    intro z _
    by_cases hz : z = 1
    · rw [hz]
      exact one_mem _
    have hzo : orderOf z = 3 := orderOf_eq_prime (hcube z) hz
    obtain ⟨a, haodd, haz⟩ := q.exists_pRegular_lift (QuotientGroup.mk'_surjective Q)
      2 Nat.prime_two z (by rw [hzo]; decide)
    have hao : orderOf a = 3 := by
      rw [← q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk a
        (Nat.prime_two.coprime_iff_not_dvd.mpr haodd), haz, hzo]
    exact ⟨a, subset_closure ⟨a.property, (Subgroup.orderOf_coe a).trans hao⟩, haz⟩
  have hsup : N ⊔ Q = ⊤ := by
    have hh := congrArg (fun A : Subgroup (Y ⧸ Q) => A.comap q) hm
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  have hN : N = ⊤ := residualY_isPPerfect M Mc N inferInstance
    (isPGroup_quotient_of_sup_eq_top N Q pCore_isPGroup hsup)
  have hYtheta : Y ≤ theta Y := by
    intro y hy
    have hh : (⟨y, hy⟩ : Y) ∈ N := by rw [hN]; trivial
    exact hh
  exact hYtheta.trans (theta_mono (Chapter14.SourcePreliminaries.sourceResidual_le M Mc))

/-- The literal order-three closure in M equals the source residual in the
extraspecial Heisenberg branch of 15.3.7. -/
public theorem extraspecial_residual_eq_theta (h : SourceInputs M Mc V T d)
    [IsExtraspecial 3 (star M (residualY M Mc))]
    (he : Nonempty (star M (residualY M Mc) ≃* HeisenbergPrime 3)) :
    residualY M Mc = theta M :=
  le_antisymm (residual_le_theta he) (theta_le_residual h he)

end CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives.ExtraspecialBranch
