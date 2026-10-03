module

public import Stellmacher.Recognition.LyonsU3Four.InvolutionCentralizerQuotients
public import Stellmacher.Recognition.LyonsU3Four.InvolutionCentralizerZStar
public import Stellmacher.MainDefs
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupTheory.SylowCentralizerCore
public import Stellmacher.Recognition.LyonsU3Four.InvolutionFusion
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Stellmacher.Recognition.LyonsU3Four.OrderFifteenNormalizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Stellmacher.Recognition.LyonsU3Four.ElementOrders
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# Involution centralizers in the N2 Lyons case

For a nonidentity element z of Z(S), the centralizer C = C_G(z) is two-local,
hence solvable under the N2 hypothesis. Z-star makes the image of Z(S)
central modulo the actual odd core O₂′(C). The further central quotient has
abelian Sylow 2-subgroups and trivial odd core; solvable Fitting
self-centralization forces its Sylow subgroup to be normal. Normality lifts
back, and the coprime normalizer theorem gives C = O₂′(C) N_C(S).

The normalizer acts transitively on the three involutions in Z(S). Thus an
ambient automizer of order fifteen gives a centralizer automizer of order
five. Schur–Zassenhaus yields an actual semidirect product S ⋊ C₅ for C/O₂′(C),
with the equivalence preserving the canonical embedding of the supplied S.
An order-five automorphism fixes precisely Z(S); consequently the centralizer
of an order-four element has odd-core quotient of order sixteen whenever
its centralizer in S has that order.

Source: Lyons, *A Characterization of the Group U₃(4)*, Trans. AMS 164
(1972), Lemma 1, pp. 372–373. This specialization uses the actual N2
hypothesis to justify the solvable Fitting argument in the residual quotient.
-/

namespace Stellmacher.Recognition.LyonsU3Four

open Subgroup
open scoped commutatorElement

public theorem involutionCentralizer_solvable_of_isNTwoGroup
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (h : SylowStructure S) {z : G}
    (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    Group.IsSolvable (centralizer ({z} : Set G)) := by
  let := centerImage_elementary S h
  exact hN _ (Theory.GroupTheory.isTwoLocal_involution_centralizer
    (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz) hz1))

public theorem centralizerReducedSylow_normal_of_isNTwoGroup
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S) {z : G}
    (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    let Q := ((centralizer ({z} : Set G) ⧸
      pPrimeCore 2 (centralizer ({z} : Set G))) ⧸ centralizerCenterClosure S z)
    (centralizerReducedSylow S hz : Subgroup Q).Normal := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := centralizer ({z} : Set G)
  let P := centralizerSylow S hz
  let O := pPrimeCore 2 C
  let q : C →* C ⧸ O := QuotientGroup.mk' O
  let Z := centralizerCenterClosure S z
  let f := centralizerReductionMap S z
  let T := centralizerReducedSylow S hz
  have hcentral := centralizerCenterModOddCore_le_center S h hz hz1
  have hZ : Z = centralizerCenterModOddCore S z :=
    centralizerCenterClosure_eq_of_le_center S z hcentral
  have hZP : Z ≤ (P : Subgroup C).map q := by
    rw [hZ]
    exact map_mono (fun x hx => centerImage_le S hx)
  have hZtwo : IsPGroup 2 Z := (P.isPGroup'.map q).to_le hZP
  have hcore : pPrimeCore 2 ((C ⧸ O) ⧸ Z) = ⊥ :=
    pPrimeCore_quotient_eq_bot_of_central_two_subgroup Z
      (by rwa [hZ]) hZtwo (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  have hkill (x : C) (hx : (x : G) ∈ centerImage S) : f x = 1 := by
    apply (QuotientGroup.eq_one_iff (q x)).mpr
    change q x ∈ Z
    rw [hZ]
    exact mem_map_of_mem q hx
  have hcomm : IsMulCommutative T := by
    apply le_centralizer_iff_isMulCommutative.mp
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hc : ⁅(b : G), (a : G)⁆ ∈ centerImage S := by
      refine ⟨⁅(⟨b, hb⟩ : S), (⟨a, ha⟩ : S)⁆, ?_, rfl⟩
      rw [h.center_eq_commutator]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    have he := hkill ⁅b, a⁆ hc
    rw [map_commutatorElement] at he
    exact commutatorElement_eq_one_iff_mul_comm.mp he
  let := hcomm
  let := involutionCentralizer_solvable_of_isNTwoGroup hN S h hz hz1
  exact T.normal_of_isMulCommutative_of_isSolvable inferInstance hcore

public theorem centralizerSylow_modOddCore_normal_of_isNTwoGroup
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S) {z : G}
    (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    ((centralizerSylow S hz : Subgroup _).map
      (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({z} : Set G))))).Normal := by
  let C := centralizer ({z} : Set G)
  let P := centralizerSylow S hz
  let q := QuotientGroup.mk' (pPrimeCore 2 C)
  let Z := centralizerCenterClosure S z
  let r := QuotientGroup.mk' Z
  have hZ : Z = centralizerCenterModOddCore S z :=
    centralizerCenterClosure_eq_of_le_center S z
      (centralizerCenterModOddCore_le_center S h hz hz1)
  have hZP : Z ≤ (P : Subgroup C).map q := by
    rw [hZ]
    exact map_mono (fun x hx => centerImage_le S hx)
  have hn := centralizerReducedSylow_normal_of_isNTwoGroup hN S h hz hz1
  change ((P : Subgroup C).map (r.comp q)).Normal at hn
  rw [← map_map] at hn
  have hc := hn.comap r
  rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZP] at hc
  exact hc

public theorem involutionCentralizer_normalizer_sup_oddCore_of_isNTwoGroup
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S) {z : G}
    (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    normalizer (centralizerSylow S hz : Set (centralizer ({z} : Set G))) ⊔
      pPrimeCore 2 (centralizer ({z} : Set G)) = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := centralizer ({z} : Set G)
  let P := centralizerSylow S hz
  let O := pPrimeCore 2 C
  let q := QuotientGroup.mk' O
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  let := centralizerSylow_modOddCore_normal_of_isNTwoGroup hN S h hz hz1
  have hn : (normalizer (P : Set C)).map q = ⊤ := by
    change (normalizer ((P : Subgroup C) : Set C)).map q = ⊤
    rw [← normalizer_map_quotient_eq_map_normalizer 2 (P : Subgroup C) O
      inferInstance (pPrimeCore_coprime_card (p := 2))]
    exact normalizer_eq_top _
  have hh := congrArg (Subgroup.comap q) hn
  simpa only [q, QuotientGroup.comap_map_mk', comap_top, sup_comm] using hh


public theorem involution_stabilizer_relIndex
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) {z : G}
    (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    (normalizer (S : Set G) ⊓ centralizer ({z} : Set G)).relIndex
      (normalizer (S : Set G)) = 3 := by
  classical
  let N := normalizer (S : Set G)
  let Z := Subgroup.center S
  let w : S := ⟨z, centerImage_le S hz⟩
  have hwZ : w ∈ Z := by
    obtain ⟨a, ha, he⟩ := hz
    have : a = w := Subtype.ext he
    exact this ▸ ha
  have hw1 : w ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  let : MulDistribMulAction N S := MulDistribMulAction.compHom S
    (S : Subgroup G).normalizerMonoidHom
  have horbit (x : S) : x ∈ MulAction.orbit N w ↔ x ∈ Z ∧ x ≠ 1 := by
    constructor
    · rintro ⟨n, rfl⟩
      let a := (S : Subgroup G).normalizerMonoidHom n
      constructor
      · exact (characteristic_iff_map_le.mp inferInstance a)
          (mem_map_of_mem a.toMonoidHom hwZ)
      · intro he
        exact hw1 (a.injective (he.trans (map_one a).symm))
    · rintro ⟨hx, hx1⟩
      obtain ⟨n, hn, he⟩ := centerImage_nonidentity_normalizer_conjugate S h hz
        (show (x : G) ∈ centerImage S from ⟨x, hx, rfl⟩)
        hz1 (fun he => hx1 (Subtype.ext he))
      refine ⟨⟨n⁻¹, N.inv_mem hn⟩, ?_⟩
      apply Subtype.ext
      change n⁻¹ * z * (n⁻¹)⁻¹ = (x : G)
      simpa only [inv_inv] using he
  have hcard : Nat.card (MulAction.orbit N w) = 3 := by
    let e : MulAction.orbit N w ≃ {v : Z // v ≠ 1} :=
      { toFun := fun x => ⟨⟨x, ((horbit x).mp x.property).1⟩,
          fun he => ((horbit x).mp x.property).2 (congrArg Subtype.val he)⟩
        invFun := fun v => ⟨v.val.val, (horbit v.val.val).mpr
          ⟨v.val.property, fun he => v.property (Subtype.ext he)⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    change Nat.card ↥(({1} : Set Z)ᶜ) = 3
    rw [Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton]
    rw [show Nat.card Z = 4 from h.center_card]
  have heq : (centralizer ({z} : Set G)).subgroupOf N =
      MulAction.stabilizer N w := by
    ext n
    change (n : G) ∈ centralizer ({z} : Set G) ↔ n • w = w
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hn
      apply Subtype.ext
      change (n : G) * z * (n : G)⁻¹ = z
      rw [hn, mul_assoc, mul_inv_cancel, mul_one]
    · intro hn
      have he := congrArg Subtype.val hn
      change (n : G) * z * (n : G)⁻¹ = z at he
      exact mul_inv_eq_iff_eq_mul.mp he
  rw [inf_relIndex_left]
  change ((centralizer ({z} : Set G)).subgroupOf N).index = 3
  rw [heq, MulAction.index_stabilizer]
  exact hcard

public theorem centralizerSylow_automizerIndex_eq_five
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (h15 : automizerIndex S = 15)
    {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    automizerIndex (centralizerSylow S hz) = 5 := by
  let C := centralizer ({z} : Set G)
  let N := normalizer (S : Set G)
  let D := (S : Subgroup G) ⊔ centralizer (S : Set G)
  let P := centralizerSylow S hz
  have hSC : (S : Subgroup G) ≤ C := sylow_le_involutionCentralizer S hz
  have hCC : centralizer (S : Set G) ≤ C := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hx z (centerImage_le S hz)).symm
  have hDC : D ≤ C := sup_le hSC hCC
  have hDN : D ≤ N := sup_le le_normalizer (Subgroup.centralizer_le_normalizer _)
  have hcent : centralizer (P : Set C) = (centralizer (S : Set G)).subgroupOf C := by
    ext c
    simp only [mem_centralizer_iff, mem_subgroupOf]
    constructor
    · intro hc s hs
      exact congrArg Subtype.val (hc ⟨s, hSC hs⟩ hs)
    · intro hc s hs
      exact Subtype.ext (hc s hs)
  have hnorm : normalizer (P : Set C) = (N ⊓ C).subgroupOf C := by
    change normalizer ((S : Subgroup G).subgroupOf C : Set C) = _
    rw [← subgroupOf_normalizer_eq hSC]
    ext x
    simp [N, mem_subgroupOf]
  have hauto : automizerIndex P = D.relIndex (N ⊓ C) := by
    unfold automizerIndex
    rw [hcent, hnorm]
    change (((S : Subgroup G).subgroupOf C) ⊔
      (centralizer (S : Set G)).subgroupOf C).relIndex _ = _
    rw [← subgroupOf_sup hSC hCC, relIndex_subgroupOf inf_le_right]
  have hm := relIndex_mul_relIndex D (N ⊓ C) N (le_inf hDN hDC) inf_le_left
  rw [involution_stabilizer_relIndex S h hz hz1] at hm
  change D.relIndex (N ⊓ C) * 3 = automizerIndex S at hm
  rw [h15] at hm
  rw [hauto]
  omega


private theorem quotient_sylow_index_of_normal
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hn : ((S : Subgroup G).map (QuotientGroup.mk' (pPrimeCore 2 G))).Normal) :
    ((S : Subgroup G).map (QuotientGroup.mk' (pPrimeCore 2 G))).index =
      automizerIndex S := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  let N := normalizer (S : Set G)
  let O := pPrimeCore 2 G
  let q := QuotientGroup.mk' O
  let f := q.comp N.subtype
  let P := (S : Subgroup G).subgroupOf N
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    change (normalizer ((S : Subgroup G) : Set G)).map (QuotientGroup.mk' O) = ⊤
    rw [← normalizer_map_quotient_eq_map_normalizer 2 (S : Subgroup G) O
        inferInstance (pPrimeCore_coprime_card (p := 2))]
    exact normalizer_eq_top _
  have hker : f.ker = pPrimeCore 2 N := by
    apply le_antisymm
    · apply le_sSup
      refine ⟨inferInstance, ?_⟩
      have he : f.ker = O.subgroupOf N := by
        ext x
        exact QuotientGroup.eq_one_iff _
      rw [he]
      rw [← card_map_of_injective N.subtype_injective, subgroupOf_map_subtype]
      exact Nat.Coprime.of_dvd_right (card_dvd_of_le (inf_le_left : O ⊓ N ≤ O))
        (pPrimeCore_coprime_card (p := 2))
    · have hm : (pPrimeCore 2 N).map f = ⊥ := by
        apply pPrimeCore_eq_bot_iff.mp (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
        · exact Subgroup.Normal.map inferInstance f hsurj
        · exact Nat.Coprime.of_dvd_right (card_map_dvd _ f)
            (pPrimeCore_coprime_card (p := 2))
      exact (map_le_iff_le_comap.mp hm.le)
  have he : (S : Subgroup G).map q = P.map f := by
    rw [show P.map f = (P.map N.subtype).map q from (map_map _ _ _).symm,
      show P.map N.subtype = (S : Subgroup G) from
        map_subgroupOf_eq_of_le (show (S : Subgroup G) ≤ N from le_normalizer)]
  rw [he, index_map, hker, f.range_eq_top_of_surjective hsurj, index_top, mul_one]
  rw [← normalizer_automizer_denominator_eq_sup_oddCore S]
  rfl
/-- The canonical embedding of the supplied Sylow into the involution centralizer
modulo its actual odd core. -/
@[expose] public def involutionCentralizerQuotientMap
    {G : Type*} [Group G] (S : Sylow 2 G) {z : G} (hz : z ∈ centerImage S) :
    S →* (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) :=
  (QuotientGroup.mk' (pPrimeCore 2 (centralizer ({z} : Set G)))).comp
    (inclusion (sylow_le_involutionCentralizer S hz))

public theorem involutionCentralizerQuotientMap_injective
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {z : G} (hz : z ∈ centerImage S) :
    Function.Injective (involutionCentralizerQuotientMap S hz) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := centralizer ({z} : Set G)
  let P := centralizerSylow S hz
  let q := QuotientGroup.mk' (pPrimeCore 2 C)
  have hi := injective_comp_subtype_of_coprime_ker q
    (by simpa only [q, QuotientGroup.ker_mk'] using
      (pPrimeCore_coprime_card (p := 2) (G := C))) (P : Subgroup C) P.isPGroup'
  intro a b he
  let aP : P := ⟨inclusion (sylow_le_involutionCentralizer S hz) a, a.property⟩
  let bP : P := ⟨inclusion (sylow_le_involutionCentralizer S hz) b, b.property⟩
  have hh : aP = bP := hi he
  exact Subtype.ext (congrArg (fun x : P => ((x : C) : G)) hh)

/-- The canonical Sylow has index five in the actual involution-centralizer
odd-core quotient in the N2 case with automizer fifteen. -/
public theorem involutionCentralizerQuotientMap_range_index
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S)
    (h15 : automizerIndex S = 15) {z : G}
    (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    (involutionCentralizerQuotientMap S hz).range.index = 5 := by
  rw [involutionCentralizerQuotientMap, MonoidHom.range_comp, inclusion_range]
  exact (quotient_sylow_index_of_normal (centralizerSylow S hz)
    (centralizerSylow_modOddCore_normal_of_isNTwoGroup hN S h hz hz1)).trans
    (centralizerSylow_automizerIndex_eq_five S h h15 hz hz1)

/-- The quotient by the actual odd core is a semidirect product of the supplied
Sylow subgroup and a cyclic group of order five. The equivalence preserves
the canonical Sylow embedding. -/
public theorem exists_orderFive_involutionCentralizer_equiv_of_isNTwoGroup
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S)
    (h15 : automizerIndex S = 15) {z : G}
    (hz : z ∈ centerImage S) (hz1 : z ≠ 1) :
    ∃ (β : MulAut S) (α : Multiplicative (ZMod 5) →* MulAut S),
      orderOf β = 5 ∧ α (Multiplicative.ofAdd (1 : ZMod 5)) = β ∧
      ∃ e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
        S ⋊[α] Multiplicative (ZMod 5),
        ∀ s : S, e (involutionCentralizerQuotientMap S hz s) =
          SemidirectProduct.inl s := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let C := centralizer ({z} : Set G)
  let O := pPrimeCore 2 C
  let Q := C ⧸ O
  let q := QuotientGroup.mk' O
  let T := (centralizerSylow S hz).mapSurjective (QuotientGroup.mk'_surjective O)
  let f := involutionCentralizerQuotientMap S hz
  let P := f.range
  have hPT : P = (T : Subgroup Q) := by
    change (involutionCentralizerQuotientMap S hz).range = (T : Subgroup Q)
    rw [involutionCentralizerQuotientMap, MonoidHom.range_comp, inclusion_range]
    rfl
  have hPN : P.Normal := by
    rw [hPT]
    exact centralizerSylow_modOddCore_normal_of_isNTwoGroup hN S h hz hz1
  let eS : S ≃* P := MonoidHom.ofInjective (involutionCentralizerQuotientMap_injective S hz)
  have hPi : P.index = 5 := involutionCentralizerQuotientMap_range_index hN S h h15 hz hz1
  have hcop : (Nat.card P).Coprime P.index := by
    rw [hPT]
    exact T.card_coprime_index
  obtain ⟨B, hB⟩ := exists_right_complement'_of_coprime hcop
  have hBcard : Nat.card B = 5 := hB.symm.index_eq_card.symm.trans hPi
  let : IsCyclic B := isCyclic_of_prime_card hBcard
  let c : Multiplicative (ZMod 5) ≃* B :=
    mulEquivOfCyclicCardEq (by simpa using hBcard.symm)
  let γ : B →* MulAut P := P.normalizerMonoidHom.comp
    (inclusion (P.normalizer_eq_top ▸ le_top))
  have hC : centralizer (P : Set Q) ≤ P := by
    have hTN : (T : Subgroup Q).Normal := hPT ▸ hPN
    have hh := T.centralizer_le_sup_pPrimeCore_of_normal
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2, sup_bot_eq] at hh
    rw [← T.coe_coe, ← hPT] at hh
    exact hh
  have hγ : Function.Injective γ := by
    apply γ.ker_eq_bot_iff.mp
    apply bot_unique
    intro b hb
    have hbC : (b : Q) ∈ centralizer (P : Set Q) := by
      have hh : inclusion (P.normalizer_eq_top ▸ le_top) b ∈ P.normalizerMonoidHom.ker := hb
      rwa [normalizerMonoidHom_ker] at hh
    exact Subtype.ext (disjoint_def.mp hB.disjoint (hC hbC) b.property)
  let α : Multiplicative (ZMod 5) →* MulAut S :=
    (MulAut.congr eS.symm).toMonoidHom.comp (γ.comp c.toMonoidHom)
  have hα : Function.Injective α :=
    (MulAut.congr eS.symm).injective.comp (hγ.comp c.injective)
  let β := α (Multiplicative.ofAdd (1 : ZMod 5))
  have hβ : orderOf β = 5 := by
    rw [show β = α (Multiplicative.ofAdd (1 : ZMod 5)) from rfl,
      orderOf_injective α hα, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  let k : P ⋊[γ] B ≃* Q := SemidirectProduct.mulEquivSubgroup hB
  let d : P ⋊[γ] B ≃* S ⋊[α] Multiplicative (ZMod 5) :=
    SemidirectProduct.congr' eS.symm c.symm
  refine ⟨β, α, hβ, rfl, k.symm.trans d, ?_⟩
  intro s
  have hk : k.symm (f s) = SemidirectProduct.inl (eS s) := by
    apply k.injective
    rw [k.apply_symm_apply]
    change f s = (SemidirectProduct.mulEquivSubgroup hB) (SemidirectProduct.inl (eS s))
    rw [SemidirectProduct.mulEquivSubgroup_apply]
    simpa only [SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      OneMemClass.coe_one, mul_one] using (MonoidHom.ofInjective_apply
        (involutionCentralizerQuotientMap_injective S hz) (x := s)).symm
  change d (k.symm (f s)) = _
  rw [hk]
  apply SemidirectProduct.ext
  · change ((SemidirectProduct.congr' eS.symm c.symm)
      (SemidirectProduct.inl (eS s))).left = s
    rw [SemidirectProduct.congr'_apply_left, SemidirectProduct.left_inl,
      eS.symm_apply_apply]
  · change ((SemidirectProduct.congr' eS.symm c.symm)
      (SemidirectProduct.inl (eS s))).right = 1
    rw [SemidirectProduct.congr'_apply_right, SemidirectProduct.right_inl, map_one]

/-- Explicit factorization retaining the actual odd core of C_G(z). -/
public theorem involutionCentralizer_factorization_of_isNTwoGroup
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S) {z : G}
    (hz : z ∈ centerImage S) (hz1 : z ≠ 1)
    (c : centralizer ({z} : Set G)) :
    ∃ o ∈ pPrimeCore 2 (centralizer ({z} : Set G)),
      ∃ n ∈ normalizer (centralizerSylow S hz : Set (centralizer ({z} : Set G))),
        o * n = c := by
  apply mem_sup_of_normal_left.mp
  rw [sup_comm, involutionCentralizer_normalizer_sup_oddCore_of_isNTwoGroup hN S h hz hz1]
  trivial

public theorem order_five_fixed_subgroup
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 5) :
    FixedPoints.subgroup (zpowers β) S = center S := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let A := zpowers β
  let F := FixedPoints.subgroup A S
  have hA : Nat.card A = 5 := by rw [Nat.card_zpowers, hβ]
  have hp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hm := hp.card_modEq_card_fixedPoints S
  change Nat.ModEq 5 (Nat.card S) (Nat.card F) at hm
  rw [h.card] at hm
  have hd : Nat.card F ∣ 2 ^ 6 := by simpa [h.card] using F.card_subgroup_dvd_card
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hne : F ≠ ⊤ := by
    intro ht
    have he : β = 1 := by
      apply DFunLike.ext
      intro s
      have hs : s ∈ F := ht ▸ mem_top s
      exact hs ⟨β, mem_zpowers β⟩
    rw [he, orderOf_one] at hβ
    omega
  have hFcard : Nat.card F = 4 := by
    rw [hcard] at hm ⊢
    interval_cases n <;> norm_num [Nat.ModEq] at hm
    · rfl
    · exact (hne (eq_top_of_card_eq F (hcard.trans h.card.symm))).elim
  have hZ : center S ≤ F := by
    let W := center S
    let := h.center_elementary
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by
      change 1 < Nat.card (center S)
      rw [h.center_card]
      decide)
    let : IsKleinFour W := ⟨h.center_card, IsElementaryAbelian.exponent_eq_prime⟩
    have hd6 : orderOf (MulAut.characteristic W β) ∣ 6 :=
      IsKleinFour.card_mulAut W ▸ orderOf_dvd_natCard _
    have hd5 : orderOf (MulAut.characteristic W β) ∣ 5 :=
      hβ ▸ orderOf_map_dvd (MulAut.characteristic W) β
    have he : MulAut.characteristic W β = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 6 5) hd6 hd5)
    intro z hz a
    have hzfix : β z = z := congrArg Subtype.val (DFunLike.congr_fun he (⟨z, hz⟩ : W))
    exact smul_eq_self_of_mem_zpowers a.property hzfix
  exact (eq_of_le_of_card_ge hZ (by rw [hFcard, h.center_card])).symm

private theorem orderFour_centralizer_le_normalSylow
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    (S : Sylow 2 G) (h : SylowStructure S) (f : S →* Q)
    (hf : Function.Injective f) (hn : f.range.Normal)
    (hi : f.range.index = 5) (hc : centralizer (f.range : Set Q) ≤ f.range)
    (t : S) (ht : orderOf t = 4) :
    centralizer ({f t} : Set Q) ≤ f.range := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P := f.range
  let D := centralizer ({f t} : Set Q)
  have hd : P.relIndex D ∣ 5 := hi ▸ relIndex_dvd_index_of_normal P D
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with he | he
  · exact relIndex_eq_one.mp he
  have hd5 : 5 ∣ Nat.card D := he ▸ relIndex_dvd_card P D
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := D) 5 hd5
  let eS : S ≃* P := MonoidHom.ofInjective hf
  let aN : normalizer (P : Set Q) := ⟨a, P.normalizer_eq_top ▸ mem_top _⟩
  let b : MulAut S := MulAut.congr eS.symm (P.normalizerMonoidHom aN)
  have hb5 : b ^ 5 = 1 := by
    have ha5 : aN ^ 5 = 1 := by
      apply Subtype.ext
      exact congrArg (fun x : D => (x : Q)) (show a ^ 5 = 1 from ha ▸ pow_orderOf_eq_one a)
    change (MulAut.congr eS.symm).toMonoidHom (P.normalizerMonoidHom aN) ^ 5 = 1
    rw [← map_pow, ← map_pow, ha5, map_one, map_one]
  have hbne : b ≠ 1 := by
    intro heq
    have hbN : P.normalizerMonoidHom aN = 1 := (MulAut.congr eS.symm).injective
      (heq.trans (map_one (MulAut.congr eS.symm)).symm)
    have hcent : (a : Q) ∈ centralizer (P : Set Q) := by
      have hh : aN ∈ P.normalizerMonoidHom.ker := hbN
      rwa [normalizerMonoidHom_ker] at hh
    obtain ⟨s, hs⟩ := hc hcent
    have hsord : orderOf s = 5 := (orderOf_injective f hf s).symm.trans
      (by rw [hs]; exact (Subgroup.orderOf_coe a).trans ha)
    have hd := orderOf_dvd_natCard s
    rw [hsord, h.card] at hd
    norm_num at hd
  have hb : orderOf b = 5 := orderOf_eq_prime hb5 hbne
  have hbt : b t = t := by
    apply eS.injective
    change eS (eS.symm (P.normalizerMonoidHom aN (eS t))) = eS t
    rw [eS.apply_symm_apply]
    apply Subtype.ext
    change (a : Q) * f t * (a : Q)⁻¹ = f t
    rw [mem_centralizer_singleton_iff.mp a.property, mul_assoc, mul_inv_cancel, mul_one]
  have htZ : t ∈ center S := by
    rw [← order_five_fixed_subgroup S h b hb]
    intro k
    exact smul_eq_self_of_mem_zpowers k.property hbt
  let := h.center_elementary
  have ht2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) t htZ
  have hd := orderOf_dvd_of_pow_eq_one ht2
  rw [ht] at hd
  norm_num at hd

/-- The order-four centralizer has odd-core quotient of order sixteen
whenever its centralizer in the supplied Sylow has order sixteen. -/
public theorem orderFour_centralizer_quotient_card_of_isNTwoGroup
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (h : SylowStructure S)
    (h15 : automizerIndex S = 15) (t : S) (ht : orderOf t = 4)
    (hct : Nat.card (centralizer ({t} : Set S)) = 16) :
    Nat.card (centralizer ({(t : G)} : Set G) ⧸
      pPrimeCore 2 (centralizer ({(t : G)} : Set G))) = 16 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let z : G := (t : G) ^ 2
  have hz : z ∈ centerImage S := ⟨t ^ 2, square_mem_center S h t, rfl⟩
  have hz1 : z ≠ 1 := by
    intro he
    have heS : t ^ 2 = 1 := Subtype.ext he
    have hd := orderOf_dvd_of_pow_eq_one heS
    rw [ht] at hd
    norm_num at hd
  let C := centralizer ({z} : Set G)
  let D := centralizer ({(t : G)} : Set G)
  let O := pPrimeCore 2 C
  let Q := C ⧸ O
  let q : C →* Q := QuotientGroup.mk' O
  let f := involutionCentralizerQuotientMap S hz
  let P := f.range
  have hn : P.Normal := by
    change (involutionCentralizerQuotientMap S hz).range.Normal
    rw [involutionCentralizerQuotientMap, MonoidHom.range_comp, inclusion_range]
    exact centralizerSylow_modOddCore_normal_of_isNTwoGroup hN S h hz hz1
  have hi : P.index = 5 := involutionCentralizerQuotientMap_range_index hN S h h15 hz hz1
  let T := (centralizerSylow S hz).mapSurjective (QuotientGroup.mk'_surjective O)
  have hPT : P = (T : Subgroup Q) := by
    change (involutionCentralizerQuotientMap S hz).range = (T : Subgroup Q)
    rw [involutionCentralizerQuotientMap, MonoidHom.range_comp, inclusion_range]
    rfl
  have hc : centralizer (P : Set Q) ≤ P := by
    have hTN : (T : Subgroup Q).Normal := hPT ▸ hn
    have hh := T.centralizer_le_sup_pPrimeCore_of_normal
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2, sup_bot_eq] at hh
    rw [← T.coe_coe, ← hPT] at hh
    exact hh
  let U := centralizer ({f t} : Set Q)
  have hUP : U ≤ P := orderFour_centralizer_le_normalSylow S h f
    (involutionCentralizerQuotientMap_injective S hz) hn hi hc t ht
  let E := centralizer ({t} : Set S)
  let g : E →* U := (f.comp E.subtype).codRestrict U (by
    intro s
    exact mem_centralizer_singleton_iff.mpr (by
      change f (s : S) * f t = f t * f (s : S)
      simpa only [← map_mul] using
        congrArg f (mem_centralizer_singleton_iff.mp s.property)))
  have hg : Function.Bijective g := by
    constructor
    · intro a b he
      apply Subtype.ext
      exact involutionCentralizerQuotientMap_injective S hz (congrArg Subtype.val he)
    · intro a
      obtain ⟨s, hs⟩ := hUP a.property
      have hsE : s ∈ E := by
        apply mem_centralizer_singleton_iff.mpr
        apply (show Function.Injective f from involutionCentralizerQuotientMap_injective S hz)
        simpa only [map_mul, hs] using mem_centralizer_singleton_iff.mp a.property
      exact ⟨⟨s, hsE⟩, Subtype.ext hs⟩
  have hUcard : Nat.card U = 16 := (Nat.card_congr (MulEquiv.ofBijective g hg).toEquiv).symm.trans hct
  have hDC : D ≤ C := by
    intro x hx
    have he := (mem_centralizer_singleton_iff.mp hx : x * (t : G) = (t : G) * x)
    exact mem_centralizer_singleton_iff.mpr ((Commute.pow_right he 2).eq)
  let tC : C := inclusion (sylow_le_involutionCentralizer S hz) t
  let k : D →* U := (q.comp (inclusion hDC)).codRestrict U (by
    intro d
    exact mem_centralizer_singleton_iff.mpr (by
      change q (inclusion hDC d) * q tC = q tC * q (inclusion hDC d)
      simpa only [← map_mul] using congrArg q
        (show inclusion hDC d * tC = tC * inclusion hDC d from
          Subtype.ext (mem_centralizer_singleton_iff.mp d.property))))
  have hk : Function.Surjective k := by
    intro a
    obtain ⟨s, hs⟩ := hg.surjective a
    let d : D := ⟨s.val, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp s.property))⟩
    exact ⟨d, hs⟩
  have hker : Nat.Coprime 2 (Nat.card k.ker) := by
    let j : k.ker →* O := ((inclusion hDC).comp k.ker.subtype).codRestrict O (by
      intro d
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val d.property)
    have hj : Function.Injective j := by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : O => ((x : C) : G)) he
    have hd : Nat.card k.ker ∣ Nat.card O := by
      rw [Nat.card_congr (MonoidHom.ofInjective hj).toEquiv]
      exact j.range.card_subgroup_dvd_card
    exact Nat.Coprime.of_dvd_right hd (pPrimeCore_coprime_card (p := 2))
  have hUcore : pPrimeCore 2 U = ⊥ := by
    apply card_eq_one.mp
    have hd : Nat.card (pPrimeCore 2 U) ∣ 2 ^ 4 := by
      simpa only [hUcard, show (2 : ℕ) ^ 4 = 16 from rfl] using (pPrimeCore 2 U).card_subgroup_dvd_card
    exact Nat.eq_one_of_dvd_coprimes
      ((pPrimeCore_coprime_card (p := 2) (G := U)).pow_left 4)
      hd dvd_rfl
  have heker : k.ker = pPrimeCore 2 D := by
    have he := pPrimeCore_comap_eq_of_surjective_coprime 2 k hk hker
    rw [hUcore] at he
    exact he
  have hcard := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective k hk).toEquiv
  rw [heker] at hcard
  exact hcard.trans hUcard

end Stellmacher.Recognition.LyonsU3Four
