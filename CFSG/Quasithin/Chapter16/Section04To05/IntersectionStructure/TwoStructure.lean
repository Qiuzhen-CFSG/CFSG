module

public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.Local
public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Structure.Involution
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.GroupTheory.CyclicSylowTwoComplement
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.Quasithin.Rank

/-!
# The order-two and cyclic-centralizer clauses of Lemma 16.4.4

The order-two case is obtained from the actual I.7.7 comparison for
`T_C R`; its factor equivalence is not replaced by a cardinality-only label.
The cyclic case uses transfer to split `C_G(L)` over its odd core and proves
that the odd core has trivial centralizer at `z`, using normality in the local
overgroup `N_G(L)`.
The center and cyclic-centralizer clauses use `HasEvenTypeCentralizers`,
supplied by `Hypothesis1611.evenType`; only its E1 consequences are needed.
No normality of either `L` or `C_G(L)` in the ambient group is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Lemma 16.4.4,
printed p.1184 (PDF p.1201).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections
open CFSG.Quasithin.ChapterI.Section06To08

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- The local I.7.7 setup with `S = T_C R`.  This is kept private because the
public interface of this file is the source-specific intersection setup. -/
private theorem tightNormalizerSetup (h : IntersectionSetup T z L g R) :
    TightNormalizerSetup ((centralizer (L : Set G)).conjBy g) g⁻¹ R
      (commutingSylow T L ⊔ R) := by
  have hc : conjSubgroup ((centralizer (L : Set G)).conjBy g) g⁻¹ =
      centralizer (L : Set G) := (centralizer (L : Set G)).conjBy_inv g
  have hST : commutingSylow T L ⊔ R ≤ (T : Subgroup G) :=
    sup_le inf_le_left h.le_sylow
  refine ⟨tight_map h.tight (MulAut.conj g), ?_, h.sylow.isPGroup, h.ne_bot,
    ?_, ?_, T.isPGroup'.of_injective (inclusion hST) (inclusion_injective _),
    ?_, le_sup_right, ?_⟩
  · intro hn
    have he : conjSubgroup ((centralizer (L : Set G)).conjBy g) g⁻¹ =
        (centralizer (L : Set G)).conjBy g := mem_normalizer_iff_map_conj_eq.mp hn
    exact h.mem_delta.2.1 (hc.symm.trans he).symm
  · simpa only [hc] using h.sylow.le
  · intro Q hp hQ hRQ
    rw [hc] at hQ
    exact (h.sylow.maximal hp hQ hRQ).le
  · rw [hc]
    exact sup_le_sup inf_le_right le_rfl
  · intro Q hp hQ hSQ
    rw [hc] at hQ
    have hcap : Q ⊓ centralizer (L : Set G) = commutingSylow T L :=
      h.toStandardSetup.commutingSylow_sylow.maximal
        (hp.of_injective (inclusion inf_le_left) (inclusion_injective _))
        inf_le_right (le_inf (le_sup_left.trans hSQ) inf_le_right)
    intro x hx
    have hm : x ∈ (centralizer (L : Set G) : Set G) * (R : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (h.sylow.le.trans inf_le_right)]
      exact hQ hx
    obtain ⟨k, hk, r, hr, rfl⟩ := hm
    have hkQ : k ∈ Q := by
      simpa only [mul_inv_cancel_right] using Q.mul_mem hx
        (Q.inv_mem (hSQ (mem_sup_right hr)))
    exact mul_mem_sup (hcap ▸ (show k ∈ Q ⊓ centralizer (L : Set G) from ⟨hkQ, hk⟩)) hr

private theorem orderTwo_model (h : IntersectionSetup T z L g R)
    (hR : Nat.card R = 2) :
    let S := commutingSylow T L ⊔ R
    (∃ m : ℕ, Nonempty (S ≃* DihedralGroup m)) ∨
      (∃ n : ℕ, ∃ hn : 4 ≤ n, Nonempty (S ≃* Semidihedral.StandardModel n hn)) := by
  dsimp
  let C := commutingSylow T L
  let S : Subgroup G := C ⊔ R
  let K' := conjSubgroup ((centralizer (L : Set G)).conjBy g) g⁻¹
  let S0 := S ⊓ K'
  let S1 := S0 ⊓ normalizer (R : Set G)
  let hn := tightNormalizerSetup h
  have hSsup : S ⊓ normalizer (R : Set G) = S1 ⊔ R := hn.normalizer_eq_sup
  have hS1card : Nat.card S1 = 2 := by
    obtain ⟨e⟩ := hn.factor_equiv
    exact (Nat.card_congr e.toEquiv).trans hR
  let : IsCyclic R := isCyclic_of_prime_card hR
  obtain ⟨r, hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := R)
  have hr2 : orderOf (r : G) = 2 := by
    simpa only [Subgroup.orderOf_coe] using hr.trans hR
  have hRzp : zpowers (r : G) = R := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr r.property)
    rw [Nat.card_zpowers, hr2, hR]
  have hS1cent : S1 = S1 ⊓ centralizer (R : Set G) := by
    apply le_antisymm
    · intro x hx
      have hx0 : x ∈ S0 ⊓ normalizer (R : Set G) := by
        simpa only [S1] using hx
      have he : S0 ⊓ normalizer (R : Set G) = S0 ⊓ centralizer (R : Set G) := by
        simpa only [S0, S, K'] using hn.normalizer_eq_centralizer
      have hx1 : x ∈ S0 ⊓ centralizer (R : Set G) := he ▸ hx0
      simpa only [S1] using (show x ∈ (S0 ⊓ normalizer (R : Set G)) ⊓
        centralizer (R : Set G) from ⟨hx0, hx1.2⟩)
    · exact inf_le_left
  let x : S := ⟨r, (le_sup_right : R ≤ S) r.property⟩
  have hSR : S1 ⊔ R ≤ S := by
    rw [← hSsup]
    exact inf_le_left
  have hcent : centralizer ({x} : Set S) = (S1 ⊔ R).subgroupOf S := by
    ext y
    constructor
    · intro hy
      have hyr : (y : G) ∈ centralizer ({(r : G)} : Set G) := by
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))
      have hyN : (y : G) ∈ normalizer (R : Set G) := by
        rw [← hRzp, normalizer_zpowers_eq_centralizer_of_order_two (r : G) hr2]
        exact hyr
      have hySup : (y : G) ∈ S1 ⊔ R := by
        rw [← hSsup]
        exact ⟨y.property, hyN⟩
      change (y : G) ∈ S1 ⊔ R
      exact hySup
    · intro hy
      change (y : G) ∈ S1 ⊔ R at hy
      have hy' : (y : G) ∈ S1 ⊔ R := hy
      have hRcent : R ≤ centralizer (S1 : Set G) := by
        rw [le_centralizer_iff]
        intro a ha b hb
        have ha' : a ∈ S1 ⊓ centralizer (R : Set G) := hS1cent ▸ ha
        exact ha'.2 b hb
      have hyprod : (y : G) ∈ (S1 : Set G) * (R : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left S1 R (hRcent.trans (centralizer_le_normalizer _))]
        exact hy'
      obtain ⟨a, ha, b, hb, hab⟩ := hyprod
      apply mem_centralizer_singleton_iff.mpr
      have hxy : (y : G) * (r : G) = (r : G) * (y : G) := by
        rw [← hab]
        have haC : a ∈ centralizer ({(r : G)} : Set G) := by
          have ha' : a ∈ S1 ⊓ centralizer (R : Set G) := hS1cent ▸ ha
          exact mem_centralizer_singleton_iff.mpr (ha'.2 (r : G) r.property).symm
        have hbC : b ∈ centralizer ({(r : G)} : Set G) := by
          rw [mem_centralizer_singleton_iff]
          exact setLike_mul_comm (s := R) hb r.property
        have hA := mem_centralizer_singleton_iff.mp haC
        have hB := mem_centralizer_singleton_iff.mp hbC
        calc
          a * b * (r : G) = a * (b * (r : G)) := by rw [mul_assoc]
          _ = a * ((r : G) * b) := by rw [hB]
          _ = (a * (r : G)) * b := by rw [mul_assoc]
          _ = ((r : G) * a) * b := by rw [hA]
          _ = (r : G) * (a * b) := by rw [mul_assoc]
      apply Subtype.ext
      exact hxy
  have hsubcard : Nat.card (↥((S1 ⊔ R : Subgroup G).subgroupOf S)) = 4 := by
    calc
      Nat.card (↥((S1 ⊔ R : Subgroup G).subgroupOf S)) = Nat.card (S1 ⊔ R : Subgroup G) :=
        Nat.card_congr (subgroupOfEquivOfLe hSR).toEquiv
      _ = 4 := by
        obtain ⟨_, hEq, ⟨e, _⟩⟩ := hn.directProduct
        have hc : Nat.card (S1 × R) = Nat.card (S1 ⊔ R : Subgroup G) := by
          have hc' := Nat.card_congr e.toEquiv
          rw [hEq] at hc'
          simpa only [S1, S0, S, K'] using hc'
        rw [← hc, Nat.card_prod, hS1card, hR]
  have hcentcard : Nat.card (centralizer ({x} : Set S)) = 4 := by
    simpa [hcent] using hsubcard
  have hP : IsPGroup 2 S := hn.hSp
  have hx2 : orderOf x = 2 := by
    exact (orderOf_coe x).symm.trans hr2
  by_cases hcard : Nat.card S = 4
  · -- The order-four branch is the Klein-four dihedral case.
    have hcardSup : Nat.card (S1 ⊔ R : Subgroup G) = 4 := by
      calc
        Nat.card (S1 ⊔ R : Subgroup G) = Nat.card ((S1 ⊔ R : Subgroup G).subgroupOf S) :=
          (Nat.card_congr (subgroupOfEquivOfLe hSR).toEquiv).symm
        _ = 4 := hsubcard
    have hSupS : S1 ⊔ R = S := by
      apply Subgroup.eq_of_le_of_card_ge (sup_le
        (show S1 ≤ S from inf_le_left.trans inf_le_left)
        (show R ≤ S from le_sup_right))
      rw [hcard, hcardSup]
    let : IsCyclic S1 := isCyclic_of_prime_card hS1card
    obtain ⟨a0, ha0⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S1)
    have hS1leS : S1 ≤ S := inf_le_left.trans inf_le_left
    let a : S := ⟨a0, hS1leS a0.property⟩
    have ha2 : orderOf a = 2 := by
      calc
        orderOf a = orderOf (a : G) := (Subgroup.orderOf_coe a).symm
        _ = orderOf (a0 : G) := rfl
        _ = orderOf a0 := Subgroup.orderOf_coe a0
        _ = 2 := ha0.trans hS1card
    let b : S := x
    have hb2 : orderOf b = 2 := hx2
    have hab : b * a * b⁻¹ = a⁻¹ := by
      have haC : (a : G) ∈ centralizer ({(r : G)} : Set G) := by
        have ha' : (a0 : G) ∈ S1 ⊓ centralizer (R : Set G) := hS1cent ▸ a0.property
        exact mem_centralizer_singleton_iff.mpr (ha'.2 (r : G) r.property).symm
      have hc : Commute (b : G) (a : G) :=
        (mem_centralizer_singleton_iff.mp haC).symm
      apply Subtype.ext
      change (b : G) * (a : G) * (b : G)⁻¹ = (a : G)⁻¹
      rw [inv_eq_self_of_orderOf_eq_two (show orderOf (b : G) = 2 from hr2),
        inv_eq_self_of_orderOf_eq_two (show orderOf (a : G) = 2 from by
          simpa only [Subgroup.orderOf_coe] using ha2)]
      calc
        (b : G) * (a : G) * (b : G) = (b : G) * ((a : G) * (b : G)) := by rw [mul_assoc]
        _ = (b : G) * ((b : G) * (a : G)) := by rw [hc.eq]
        _ = ((b : G) * (b : G)) * (a : G) := by rw [mul_assoc]
        _ = (a : G) := by
          have hbb : (b : G) * (b : G) = 1 := by
            change (r : G) * (r : G) = 1
            simpa [pow_two, hr2] using (pow_orderOf_eq_one (r : G))
          rw [hbb, one_mul]
    have hza : zpowers a = S1.subgroupOf S := by
      have haS1 : a ∈ S1.subgroupOf S := by
        change (a : G) ∈ S1
        exact a0.property
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr haS1)
      rw [Nat.card_zpowers, ha2]
      simpa only [Nat.card_congr (subgroupOfEquivOfLe hS1leS).toEquiv] using hS1card.le
    have hzb : zpowers b = R.subgroupOf S := by
      have hbR : b ∈ R.subgroupOf S := by
        change (b : G) ∈ R
        exact r.property
      apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hbR)
      rw [Nat.card_zpowers, hb2]
      simpa only [Nat.card_congr (subgroupOfEquivOfLe (show R ≤ S from le_sup_right)).toEquiv] using hR.le
    have hgen : Subgroup.closure ({a, b} : Set S) = ⊤ := by
      apply top_unique
      have htop : S1.subgroupOf S ⊔ R.subgroupOf S = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hS1leS (show R ≤ S from le_sup_right), hSupS]
        exact Subgroup.subgroupOf_eq_top.mpr le_rfl
      rw [← htop]
      apply sup_le
      · rw [← hza]
        exact zpowers_le.mpr (Subgroup.subset_closure (by simp))
      · rw [← hzb]
        exact zpowers_le.mpr (Subgroup.subset_closure (by simp))
    exact Or.inl ⟨2, dihedralGroup_equiv_of_presentation (by decide)
      a b (by simp [← ha2])
      (by simpa [hb2] using pow_orderOf_eq_one b) hab hgen hcard⟩
  · have hxZ : x ∉ center S := by
      intro hxZ
      have : centralizer ({x} : Set S) = ⊤ := by
        apply le_antisymm le_top
        intro y hy
        rw [mem_centralizer_singleton_iff]
        exact mem_center_iff.mp hxZ y
      rw [this] at hcentcard
      simp at hcentcard
      exact hcard hcentcard
    rcases exists_dihedral_or_semidihedral_of_involution_centralizer_card_four
      hP x hx2 hxZ hcentcard with hd | hs
    · exact Or.inl hd
    · rcases hs with ⟨n, hn, hc, a, b, ha, hb, hab, hgen⟩
      exact Or.inr ⟨n, hn,
        Semidihedral.standardModel_equiv_of_presentation hn a b ha hb hab hgen hc⟩

/-- The two-group model in the order-two branch of 16.4.4(1). -/
theorem IntersectionSetup.order_two_model (h : IntersectionSetup T z L g R)
    (hR : Nat.card R = 2) :
    let S := R ⊔ commutingSylow T L
    (∃ m : ℕ, Nonempty (S ≃* DihedralGroup m)) ∨
      (∃ n : ℕ, ∃ hn : 4 ≤ n, Nonempty (S ≃* Semidihedral.StandardModel n hn)) := by
  rw [sup_comm R (commutingSylow T L)]
  exact orderTwo_model h hR

/-- The two-rank in the order-two branch is exactly two. -/
theorem IntersectionSetup.order_two_primeRank (h : IntersectionSetup T z L g R)
    (hR : Nat.card R = 2) :
    primeRank 2 (R ⊔ commutingSylow T L : Subgroup G) = 2 := by
  let C : Subgroup G := commutingSylow T L
  have hP : IsPGroup 2 (C ⊔ R : Subgroup G) := (tightNormalizerSetup h).hSp
  let : IsCyclic R := isCyclic_of_prime_card hR
  obtain ⟨r, hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := R)
  have hr2 : orderOf (r : G) = 2 := by
    simpa only [Subgroup.orderOf_coe] using hr.trans hR
  have hzr : (r : G) ∈ centralizer ({z} : Set G) := by
    exact h.sylow_centralizes (h.le_sylow r.property)
  have hzC : z ∈ C := h.toStandardSetup.z_mem_commutingSylow
  have hrnot : (r : G) ∉ zpowers z := by
    classical
    intro hrz
    have hrC : (r : G) ∈ C := (zpowers_le.mpr hzC) hrz
    have hm : (r : G) ∈ R ⊓ centralizer (L : Set G) :=
      ⟨r.property, (show C ≤ centralizer (L : Set G) from inf_le_right) hrC⟩
    have hrne : (r : G) ≠ 1 := by
      intro he
      simp [he] at hr2
    apply hrne
    simpa only [h.normalizer_structure.2.2.2, mem_bot] using hm
  have hfix : zpowers z ≤ centralizer ({(r : G)} : Set G) := by
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hzr).symm
  have hsmall : primeRank 2 (zpowers z) + 1 ≤
      primeRank 2 (zpowers z ⊔ zpowers (r : G) : Subgroup G) :=
    primeRank_succ_le_sup_zpowers (zpowers z) (r : G) hr2 hfix hrnot
  have hjoin : zpowers z ⊔ zpowers (r : G) ≤ (R ⊔ C : Subgroup G) := by
    apply sup_le
    · exact (zpowers_le.mpr ((le_sup_right : C ≤ (R ⊔ C : Subgroup G)) hzC))
    · exact (zpowers_le.mpr ((le_sup_left : R ≤ (R ⊔ C : Subgroup G)) r.property))
  have hlow : 2 ≤ primeRank 2 (R ⊔ C : Subgroup G) := by
    have hzrank : 1 ≤ primeRank 2 (zpowers z) := by
      let z' : zpowers z := ⟨z, mem_zpowers z⟩
      have hz' : orderOf z' = 2 := (orderOf_coe z').symm.trans h.involution
      let : IsElementaryAbelian 2 (zpowers z') :=
        IsElementaryAbelian.zpowers_of_pow_eq_one (hz' ▸ pow_orderOf_eq_one z')
      exact IsElementaryAbelian.primeRank_ge_of_card (zpowers z')
        (by simpa only [Nat.card_zpowers, pow_one] using hz')
    exact le_trans (by omega : 2 ≤ primeRank 2 (zpowers z ⊔ zpowers (r : G) : Subgroup G))
      ((primeRank_mono 2 hjoin))
  rcases orderTwo_model h hR with hd | hs
  · obtain ⟨m, ⟨e⟩⟩ := hd
    let : Finite (DihedralGroup m) :=
      Finite.of_injective (e.symm : DihedralGroup m → ↥(commutingSylow T L ⊔ R))
        e.symm.injective
    have hD : IsPGroup 2 (DihedralGroup m) := hP.of_equiv e
    obtain ⟨k, hk⟩ := hD.exists_card_eq
    rw [DihedralGroup.nat_card] at hk
    have hkpos : 1 ≤ k := by
      by_contra hk0
      have : k = 0 := by omega
      simp only [this, pow_zero] at hk
      omega
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ]
    have hm : m = 2 ^ (k - 1) := by
      omega
    have hu := dihedral_rank_le_two (k - 1)
    have hu' : primeRank 2 (R ⊔ C : Subgroup G) ≤ 2 := by
      calc
        primeRank 2 (R ⊔ C : Subgroup G) = primeRank 2 (C ⊔ R : Subgroup G) := by
          rw [sup_comm]
        _ = primeRank 2 (DihedralGroup m) := primeRank_congr 2 e
        _ = primeRank 2 (DihedralGroup (2 ^ (k - 1))) := by rw [hm]
        _ ≤ 2 := hu
    exact le_antisymm hu' hlow
  · obtain ⟨n, hn, ⟨e⟩⟩ := hs
    have hu := semidihedral_rank_le_two n hn
    have hu' : primeRank 2 (R ⊔ C : Subgroup G) ≤ 2 := by
      calc
        primeRank 2 (R ⊔ C : Subgroup G) = primeRank 2 (C ⊔ R : Subgroup G) := by
          rw [sup_comm]
        _ = primeRank 2 (Semidihedral.StandardModel n hn) := primeRank_congr 2 e
        _ ≤ 2 := hu
    exact le_antisymm hu' hlow

/-- Relative normality puts the odd-core fixed subgroup in the local odd core. -/
theorem StandardSetup.oddCore_centralizer_le (h : StandardSetup T z L) :
    ((pPrimeCore 2 (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype).subgroupOf
      (involutionCentralizer z) ≤ pPrimeCore 2 (involutionCentralizer z) := by
  let K := centralizer (L : Set G)
  let O := (pPrimeCore 2 K).map K.subtype
  let C := involutionCentralizer z
  have hCN : C ≤ normalizer (O : Set G) := by
    apply le_trans (h.normalizers_eq ▸ h.centralizer_z_le)
    exact normalizer_le_normalizer_characteristic_image K (pPrimeCore 2 K)
  let : (O.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hCN
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  have hcop : Nat.Coprime 2 (Nat.card O) := by
    rw [show Nat.card O = Nat.card (pPrimeCore 2 K) from card_map_of_injective K.subtype_injective]
    exact pPrimeCore_coprime_card
  have hd : Nat.card (O.subgroupOf C) ∣ Nat.card O := by
    let f : O.subgroupOf C →* O :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact card_dvd_of_injective f (fun _ _ he => Subtype.ext
      (Subtype.ext (congrArg (fun t : O => (t : G)) he)))
  exact hcop.of_dvd_right hd

/-- The multiplicative splitting of K over its embedded odd core. -/
theorem StandardSetup.cyclic_commutingSylow_product (h : StandardSetup T z L)
    (hcyc : IsCyclic (commutingSylow T L)) :
    (centralizer (L : Set G) : Set G) = (commutingSylow T L : Set G) *
      ((pPrimeCore 2 (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype : Set G) := by
  let K := centralizer (L : Set G)
  obtain ⟨S, hS⟩ := h.commutingSylow_sylow
  have hcycS : IsCyclic S := by
    let e := (S : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective
    exact (e.trans (MulEquiv.subgroupCongr hS)).isCyclic.mpr hcyc
  have heven : 2 ∣ Nat.card K := by
    have hz : orderOf (⟨z, h.z_mem_commutingSylow.2⟩ : K) = 2 :=
      (orderOf_coe _).symm.trans h.involution
    exact hz ▸ orderOf_dvd_natCard (⟨z, h.z_mem_commutingSylow.2⟩ : K)
  have hc := S.isComplement'_pPrimeCore_of_isCyclic hcycS heven
  apply Set.ext
  intro x
  constructor
  · intro hx
    obtain ⟨⟨a, b⟩, hab⟩ := hc.2 (⟨x, hx⟩ : K)
    refine ⟨a, ?_, b, ?_, congrArg Subtype.val hab⟩
    · rw [← hS]
      exact mem_map_of_mem K.subtype a.property
    · exact mem_map_of_mem K.subtype b.property
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact K.mul_mem ha.2 (map_subtype_le _ hb)

/-- E1 kills the odd-core factor fixed by z. Consequently the local centralizer
inside K is exactly the cyclic Sylow subgroup, as in 16.4.4(2). -/
theorem StandardSetup.cyclic_commutingSylow_centralizer
    (h : StandardSetup T z L) (hE : HasEvenTypeCentralizers G)
    (hcyc : IsCyclic (commutingSylow T L)) :
    centralizer (L : Set G) ⊓ involutionCentralizer z = commutingSylow T L := by
  let K := centralizer (L : Set G)
  let O := (pPrimeCore 2 K).map K.subtype
  let C := involutionCentralizer z
  have hfix : O.subgroupOf C = ⊥ :=
    le_bot_iff.mp ((hE.oddCore z h.involution) ▸ h.oddCore_centralizer_le)
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (commutingSylow T L : Set G) * (O : Set G) := by
      rw [← h.cyclic_commutingSylow_product hcyc]
      exact hx.1
    obtain ⟨a, ha, b, hb, hab⟩ := hxprod
    change a * b = x at hab
    have hbz : b ∈ C := by
      have habz : a * b ∈ C := by
        rw [hab]
        exact hx.2
      simpa only [inv_mul_cancel_left] using
        C.mul_mem (C.inv_mem (h.sylow_centralizes ha.1)) habz
    have hb1 : b = 1 := by
      have hh : (⟨b, hbz⟩ : C) ∈ O.subgroupOf C := hb
      rw [hfix, mem_bot] at hh
      exact congrArg Subtype.val hh
    have hax : a = x := by simpa only [hb1, mul_one] using hab
    exact hax ▸ ha
  · exact le_inf inf_le_right (inf_le_left.trans h.sylow_centralizes)

/-- The center assertion in 16.4.4(1). E1 makes the component center a
two-group; its nontrivial intersection with the center of T then lies
in the already identified order-two centralizer of R. -/
theorem IntersectionSetup.z_mem_component_center (h : IntersectionSetup T z L g R)
    (hE : HasEvenTypeCentralizers G)
    (hR : Nat.card R = 2) (hZ : center L ≠ ⊥) :
    z ∈ (center L).map L.subtype := by
  let Z := (center L).map L.subtype
  have hZ2 : IsPGroup 2 Z := by
    change IsPGroup 2 ((center L).map L.subtype)
    rw [hE.component_center_eq_twoCore h.involution h.component]
    exact pCore_isPGroup.map L.subtype
  have hTN : (T : Subgroup G) ≤ normalizer (Z : Set G) :=
    h.sylow_normalizes.trans (normalizer_le_normalizer_characteristic_image L (center L))
  have hZT : Z ≤ (T : Subgroup G) := by
    have hs := T.is_maximal' (hZ2.to_sup_of_normal_left' T.isPGroup' hTN)
      (le_sup_right : (T : Subgroup G) ≤ Z ⊔ (T : Subgroup G))
    exact hs ▸ (le_sup_left : Z ≤ Z ⊔ (T : Subgroup G))
  have hZK : Z ≤ centralizer (L : Set G) := by
    rintro x ⟨a, ha, rfl⟩ b hb
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨b, hb⟩)
  let N := Z.subgroupOf (T : Subgroup G)
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hZT).mpr hTN
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  have hN : Nontrivial N := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    have hc : Nat.card N = Nat.card (center L) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hZT).toEquiv]
      exact card_map_of_injective L.subtype_injective
    rw [hc]
    let : Nontrivial (center L) := (nontrivial_iff_ne_bot _).mpr hZ
    exact Finite.one_lt_card
  obtain ⟨U, _, hUN, hUcard, hUc⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N hN
  let V := U.map (T : Subgroup G).subtype
  have hVZ : V ≤ Z := by
    rintro x ⟨a, ha, rfl⟩
    exact hUN ha
  have hV : V ≤ commutingSylow T L ⊓ centralizer (R : Set G) := by
    rintro x ⟨a, ha, rfl⟩
    refine ⟨⟨a.property, hZK (hUN ha)⟩, ?_⟩
    intro r hr
    exact congrArg Subtype.val (mem_center_iff.mp (hUc ha) ⟨r, h.le_sylow hr⟩)
  have he : V = commutingSylow T L ⊓ centralizer (R : Set G) := by
    apply eq_of_le_of_card_ge hV
    rw [h.centralizer_eq_zpowers_of_card_two hR |>.2]
    rw [show Nat.card V = Nat.card U from card_map_of_injective (T : Subgroup G).subtype_injective,
      hUcard]
  apply hVZ
  rw [he, h.centralizer_eq_zpowers_of_card_two hR |>.1]
  exact mem_zpowers z

end CFSG.Quasithin.Chapter16.Intersections
