module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCoreQuotient
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Completion of the original nonbinary larger-core argument

Let P=O₂(KS), choose the KS-invariant elementary lift A, and put C=C_P(A).
The earlier exact deficit supplies an outside maximum elementary subgroup E
with C=A(C∩E) and P∩E not contained in C. Hence P∩E centralizes C modulo U.
The largest subgroup of P centralizing C modulo U is K-invariant; the
irreducible section P/C forces this subgroup to be P.

An element of P acting trivially on Q/U acts on each complementary elementary
lift through the original two-section kernel. The checked nonbinary action
normalizer matches both actions with a single element of Q. Since C_P(Q)=U,
the kernel is exactly Q. It follows that C=A and P=Q. The same maximum
subgroup then gives the original Sylow two-rank 6n.

These are C.1.35(3)--(4), applied to the original subgroups in 4.3.11.
MSData remains an explicit earlier input: its construction, secondary
component geometry, original A₅ application and terminal exclusions remain
with qt-d-1222-rankone-uniqueness-nonblock. NonblockMSCoreApplications uses
the core identity in the corrected secondary-source construction and sieve.
Source: Aschbacher--Smith, C.1.35, printed pp.138--139, and 4.3.11, p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

private theorem core_le_joinCore : Q c ≤ (K c ⊔ S c).pCoreIn 2 := by
  rw [←sylow_join_commutator_eq c]
  exact le_normalizer_iff_commutator_le_left.mp
    ((le_sup_left : K c ≤ K c ⊔ S c).trans join_normalizes_joinCore)

omit [Finite G] in
private theorem centerIn_eq (X : Subgroup G) :
    (center X).map X.subtype = X ⊓ Subgroup.centralizer (X : Set G) := by
  ext x
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,mem_centralizer_iff.mpr ?_⟩
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  · rintro ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hc y y.property)

omit [Finite G] in
private theorem liftAction_normalizes (A : invariantCoreLifts c)
    (x : normalizer (A.val : Set G)) (hx : (x : G) ∈ normalizer (K c : Set G)) :
    A.val.normalizerMonoidHom x ∈
      normalizer ((invariantLiftAction A).range : Set (MulAut A.val)) := by
  apply mem_normalizer_iff.mpr
  intro a
  constructor
  · rintro ⟨k,rfl⟩
    let k' : K c := ⟨(x : G)*k*(x : G)⁻¹,(mem_normalizer_iff.mp hx k).mp k.property⟩
    refine ⟨k',?_⟩
    have he : inclusion A.property.2.2 k' = x * inclusion A.property.2.2 k * x⁻¹ :=
      Subtype.ext rfl
    change A.val.normalizerMonoidHom (inclusion A.property.2.2 k') = _
    rw [he,map_mul,map_mul,map_inv]
    rfl
  · rintro ⟨k,hk⟩
    let k' : K c := ⟨(x : G)⁻¹*k*x,by simpa only [inv_inv] using (mem_normalizer_iff.mp ((normalizer (K c : Set G)).inv_mem hx) k).mp k.property⟩
    refine ⟨k',?_⟩
    have he : inclusion A.property.2.2 k' = x⁻¹ * inclusion A.property.2.2 k * x :=
      Subtype.ext rfl
    change A.val.normalizerMonoidHom (inclusion A.property.2.2 k') = a
    rw [he,map_mul,map_mul,map_inv]
    change (A.val.normalizerMonoidHom x)⁻¹ * invariantLiftAction A k * A.val.normalizerMonoidHom x = a
    rw [hk]
    group

private theorem centralQuotient_action_matches (d : MSData c n) (hn : 1 < n)
    (A : invariantCoreLifts c) (x : G)
    (hx : x ∈ commutatorPreimage ((K c ⊔ S c).pCoreIn 2) (Q c) (U c)) :
    ∃ q ∈ Q c, ∀ a ∈ A.val, x*a*x⁻¹ = q*a*q⁻¹ := by
  let P := (K c ⊔ S c).pCoreIn 2
  let D := commutatorPreimage P (Q c) (U c)
  have hDP : D ≤ P := commutatorPreimage_le _ _ _
  have hDQ : ⁅D,Q c⁆ ≤ U c := commutator_commutatorPreimage_le _ _ _
    (d.joinCore_centralizes_center.trans (Subgroup.centralizer_le_normalizer _))
  have hDA : D ≤ normalizer (A.val : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      (((commutator_mono le_rfl A.property.2.1.le).trans hDQ).trans A.property.1.le)
  let xN : normalizer (A.val : Set G) := ⟨x,hDA hx⟩
  have hxR : A.val.normalizerMonoidHom xN ∈ sectionKernel ((U c).subgroupOf A.val) := by
    constructor
    · intro a
      exact hDQ (commutator_mem_commutator hx (A.property.2.1.le a.property))
    · intro a ha
      apply Subtype.ext
      change x*(a:G)*x⁻¹ = a
      rw [←mem_centralizer_iff.mp (d.joinCore_centralizes_center (hDP hx)) a ha,
        mul_inv_cancel_right]
  have hxK : x ∈ normalizer (K c : Set G) :=
    (sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le))
      (pCoreIn_le 2 _ (hDP hx))
  obtain ⟨q,hq⟩ := (d.invariantLift_sectionKernel_normalizer hn A).le
    ⟨hxR,liftAction_normalizes A xN hxK⟩
  refine ⟨q,q.property,?_⟩
  intro a ha
  exact (congrArg Subtype.val (DFunLike.congr_fun hq (⟨a,ha⟩ : A.val))).symm

/-- The kernel on the original Q/U inside the larger core is exactly Q. -/
theorem MSData.joinCore_centralQuotient_kernel_eq (d : MSData c n) (hn : 1 < n) :
    commutatorPreimage ((K c ⊔ S c).pCoreIn 2) (Q c) (U c) = Q c := by
  obtain ⟨A,B,hAe,hBe,hAc,hBc,hAn,hBn,hi,hs,hCA,hCB⟩ :=
    d.exists_selfCentralizing_elementary_core_decomposition
  let := hAe
  let := hBe
  have hQK : Q c ≤ K c := (Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 _) le_rfl)
  have hAQ : A ≤ Q c := le_sup_left.trans_eq hs
  have hBQ : B ≤ Q c := le_sup_right.trans_eq hs
  have hAstrict : A < Q c := by
    apply lt_of_le_of_ne hAQ
    intro he
    have hh := hAc
    rw [he,d.core_card] at hh
    have hp : (2:ℕ)^(6*n) < 2^(9*n) := pow_lt_pow_right₀ (by decide) (by omega)
    omega
  have hBstrict : B < Q c := by
    apply lt_of_le_of_ne hBQ
    intro he
    have hh := hBc
    rw [he,d.core_card] at hh
    have hp : (2:ℕ)^(6*n) < 2^(9*n) := pow_lt_pow_right₀ (by decide) (by omega)
    omega
  have hUA : U c < A := by
    apply lt_of_le_of_ne (hi ▸ inf_le_left)
    intro he
    have hc : Q c ≤ Subgroup.centralizer (A : Set G) := by
      rw [←he]
      exact le_centralizer_iff.mp ((centerIn_eq (Q c)).le.trans inf_le_right)
    have hh := hCA
    rw [inf_eq_left.mpr hc] at hh
    exact hAstrict.ne hh.symm
  have hUB : U c < B := by
    apply lt_of_le_of_ne (hi ▸ inf_le_right)
    intro he
    have hc : Q c ≤ Subgroup.centralizer (B : Set G) := by
      rw [←he]
      exact le_centralizer_iff.mp ((centerIn_eq (Q c)).le.trans inf_le_right)
    have hh := hCB
    rw [inf_eq_left.mpr hc] at hh
    exact hBstrict.ne hh.symm
  let a : invariantCoreLifts c := ⟨A,hUA,hAstrict,hAn⟩
  let b : invariantCoreLifts c := ⟨B,hUB,hBstrict,hBn⟩
  have hfactor (q : G) (hq : q ∈ Q c) : ∃ x ∈ A, ∃ y ∈ B, x*y=q := by
    have hm : q ∈ A ⊔ B := hs.symm ▸ hq
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left A B (hBQ.trans (hQK.trans hAn))] at hm
    exact hm
  apply le_antisymm ?_ (le_commutatorPreimage core_le_joinCore ?_)
  · intro k hk
    obtain ⟨q₁,hq₁,h₁⟩ := centralQuotient_action_matches d hn a k hk
    obtain ⟨q₂,hq₂,h₂⟩ := centralQuotient_action_matches d hn b k hk
    obtain ⟨a₁,ha₁,b₁,hb₁,rfl⟩ := hfactor q₁ hq₁
    obtain ⟨a₂,ha₂,b₂,hb₂,rfl⟩ := hfactor q₂ hq₂
    have hmatchA (x : G) (hx : x ∈ A) :
        k*x*k⁻¹ = (a₂*b₁)*x*(a₂*b₁)⁻¹ := by
      rw [h₁ x hx]
      have hy : b₁*x*b₁⁻¹ ∈ A := (mem_normalizer_iff.mp (hAn (hBQ.trans hQK hb₁)) x).mp hx
      have hc₁ := mem_centralizer_iff.mp (le_centralizer A ha₁) _ hy
      have hc₂ := mem_centralizer_iff.mp (le_centralizer A ha₂) _ hy
      calc
        (a₁*b₁)*x*(a₁*b₁)⁻¹ = a₁*(b₁*x*b₁⁻¹)*a₁⁻¹ := by group
        _ = b₁*x*b₁⁻¹ := by rw [←hc₁,mul_inv_cancel_right]
        _ = a₂*(b₁*x*b₁⁻¹)*a₂⁻¹ := by rw [←hc₂,mul_inv_cancel_right]
        _ = (a₂*b₁)*x*(a₂*b₁)⁻¹ := by group
    have hmatchB (x : G) (hx : x ∈ B) :
        k*x*k⁻¹ = (a₂*b₁)*x*(a₂*b₁)⁻¹ := by
      rw [h₂ x hx]
      have hc₁ := mem_centralizer_iff.mp (le_centralizer B hb₁) x hx
      have hc₂ := mem_centralizer_iff.mp (le_centralizer B hb₂) x hx
      calc
        (a₂*b₂)*x*(a₂*b₂)⁻¹ = a₂*(b₂*x*b₂⁻¹)*a₂⁻¹ := by group
        _ = a₂*x*a₂⁻¹ := by rw [←hc₂,mul_inv_cancel_right]
        _ = a₂*(b₁*x*b₁⁻¹)*a₂⁻¹ := by rw [←hc₁,mul_inv_cancel_right]
        _ = (a₂*b₁)*x*(a₂*b₁)⁻¹ := by group
    let q := a₂*b₁
    have hq : q ∈ Q c := (Q c).mul_mem (hAQ ha₂) (hBQ hb₁)
    have hcent : q⁻¹*k ∈ Subgroup.centralizer (Q c : Set G) := by
      have hAcent : q⁻¹*k ∈ Subgroup.centralizer (A : Set G) := by
        apply mem_centralizer_iff.mpr
        intro x hx
        have hh := congrArg (fun z : G => q⁻¹*z*k) (hmatchA x hx)
        dsimp [q] at hh ⊢
        group at hh ⊢
        exact hh.symm
      have hBcent : q⁻¹*k ∈ Subgroup.centralizer (B : Set G) := by
        apply mem_centralizer_iff.mpr
        intro x hx
        have hh := congrArg (fun z : G => q⁻¹*z*k) (hmatchB x hx)
        dsimp [q] at hh ⊢
        group at hh ⊢
        exact hh.symm
      apply mem_centralizer_iff.mpr
      intro x hx
      obtain ⟨y,hy,z,hz,rfl⟩ := hfactor x hx
      exact (Commute.mul_left (show Commute y (q⁻¹*k) from mem_centralizer_iff.mp hAcent y hy)
          (show Commute z (q⁻¹*k) from mem_centralizer_iff.mp hBcent z hz)).eq
    have hP : q⁻¹*k ∈ (K c ⊔ S c).pCoreIn 2 :=
      ((K c ⊔ S c).pCoreIn 2).mul_mem
        (((K c ⊔ S c).pCoreIn 2).inv_mem (core_le_joinCore hq)) (commutatorPreimage_le _ _ _ hk)
    have hu := (d.joinCore_coreCentralizer_eq hn).le ⟨hP,hcent⟩
    have hh := (Q c).mul_mem hq ((map_subtype_le _) hu)
    simpa only [mul_inv_cancel_left] using hh
  · rw [← d.core_derived_eq_center]
    change ⁅Q c,Q c⁆ ≤ (⁅⊤,⊤⁆ : Subgroup (Q c)).map (Q c).subtype
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]

/-- The outside maximum elementary subgroup forces the elementary factor
central in P modulo the original U. This uses irreducibility, not just orders. -/
theorem MSData.joinCore_liftCentralizer_commutator_le (d : MSData c n) (hn : 1 < n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G)) :
    ⁅(K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A.val : Set G),
      (K c ⊔ S c).pCoreIn 2⁆ ≤ U c := by
  let P := (K c ⊔ S c).pCoreIn 2
  let C := P ⊓ Subgroup.centralizer (A.val : Set G)
  let D := commutatorPreimage P C (U c)
  let := d.joinCore_liftCentralizer_elementary A
  let := (d.invariantCoreLifts_elementary A).1
  have hPU : P ≤ normalizer (U c : Set G) :=
    d.joinCore_centralizes_center.trans (Subgroup.centralizer_le_normalizer _)
  have hKC : K c ≤ normalizer (C : Set G) :=
    (le_inf ((le_sup_left : K c ≤ K c ⊔ S c).trans join_normalizes_joinCore)
      (A.property.2.2.trans (normalizer_le_normalizer_centralizer A.val))).trans
        inf_normalizer_le_normalizer_inf
  have hCD : C ≤ D := le_commutatorPreimage inf_le_left (by
    exact (commutator_self_eq_bot_iff.mpr inferInstance).le.trans bot_le)
  have hAC : A.val ≤ C := le_inf (A.property.2.1.le.trans core_le_joinCore)
    (le_centralizer A.val)
  have hDP : D ≤ P := commutatorPreimage_le _ _ _
  have hKD : K c ≤ normalizer (D : Set G) :=
    commutatorPreimage_normalized P C (U c) (K c) hPU
      ((le_sup_left : K c ≤ K c ⊔ S c).trans join_normalizes_joinCore)
      hKC d.natural.2.1
  obtain ⟨E,hE,hout⟩ := d.exists_maxElementary_outside_joinCore
  let := hE.2.1
  have hgen : C = A.val ⊔ (C ⊓ E) :=
    (d.maxElementary_core_equality hn A hA E hE hout).2.2
  have hPA : ⁅P,A.val⁆ ≤ U c := by
    apply commutator_le.mpr
    intro p hp a ha
    exact (d.joinCore_liftAction_mem_sectionKernel A hA p hp).1 ⟨a,ha⟩
  have hCB : ⁅C,P ⊓ E⁆ ≤ U c := by
    have hpre : C ≤ commutatorPreimage P (P ⊓ E) (U c) := by
      rw [hgen]
      apply sup_le
      · apply le_commutatorPreimage (hAC.trans inf_le_left)
        rw [commutator_comm]
        exact (commutator_mono inf_le_left le_rfl).trans hPA
      · apply le_commutatorPreimage (inf_le_left.trans inf_le_left)
        have hb : ⁅C ⊓ E,P ⊓ E⁆ = ⊥ :=
          commutator_eq_bot_iff_le_centralizer.mpr
            (inf_le_right.trans ((le_centralizer E).trans (centralizer_le inf_le_right)))
        rw [hb]
        exact bot_le
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hPU)
  have hBD : P ⊓ E ≤ D := le_commutatorPreimage inf_le_left
    (by rwa [commutator_comm])
  have hQD : Q c ≤ D := by
    by_contra hnot
    have hQA : Q c ⊓ D = A.val := by
      have hAD : A.val ≤ Q c ⊓ D := le_inf A.property.2.1.le (hAC.trans hCD)
      let a : invariantCoreLifts c := ⟨Q c ⊓ D,
        A.property.1.trans_le hAD,
        lt_of_le_of_ne inf_le_left (fun he => hnot (he.ge.trans inf_le_right)),
        (le_inf d.doubleDual.2.1 hKD).trans inf_normalizer_le_normalizer_inf⟩
      have hc : Nat.card (Q c ⊓ D : Subgroup G) = Nat.card A.val :=
        (d.invariantCoreLifts_elementary a).2.trans
          (d.invariantCoreLifts_elementary A).2.symm
      exact (eq_of_le_of_card_ge hAD hc.le).symm
    have hDC : D ≤ C := by
      intro x hx
      have hxP : x ∈ Q c ⊔ C :=
        (d.joinCore_eq_core_sup_liftCentralizer hn A hA).1.le (hDP hx)
      have hQC : Q c ≤ normalizer (C : Set G) :=
        ((Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 _) le_rfl)).trans hKC
      have hxprod : x ∈ (Q c : Set G) * (C : Set G) := by
        rwa [←coe_mul_of_left_le_normalizer_right (Q c) C hQC]
      obtain ⟨q,hq,z,hz,rfl⟩ := hxprod
      have hqD : q ∈ D := by
        have hh := D.mul_mem hx (D.inv_mem (hCD hz))
        simpa only [mul_inv_cancel_right] using hh
      exact C.mul_mem (hAC (hQA.le ⟨hq,hqD⟩)) hz
    exact d.maxElementary_not_le_liftCentralizer A hA E hE hout (hBD.trans hDC)
  have hPD : P ≤ D := by
    exact (d.joinCore_eq_core_sup_liftCentralizer hn A hA).1.le.trans (sup_le hQD hCD)
  rw [commutator_comm]
  exact (commutator_mono hPD le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hPU)

/-- The excess elementary centralizer factor vanishes in the original
nonbinary MS geometry. -/
theorem MSData.joinCore_liftCentralizer_eq (d : MSData c n) (hn : 1 < n)
    (A : invariantCoreLifts c) (hA : K c ⊔ S c ≤ normalizer (A.val : Set G)) :
    (K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A.val : Set G) = A.val := by
  let C := (K c ⊔ S c).pCoreIn 2 ⊓ Subgroup.centralizer (A.val : Set G)
  have hCQ : C ≤ Q c := by
    rw [←d.joinCore_centralQuotient_kernel_eq hn]
    exact le_commutatorPreimage inf_le_left
      ((commutator_mono le_rfl core_le_joinCore).trans
        (d.joinCore_liftCentralizer_commutator_le hn A hA))
  exact (inf_eq_right.mpr hCQ).symm.trans
    (d.joinCore_eq_core_sup_liftCentralizer hn A hA).2

/-- Original 4.3.11's core identity, conditional only on the existing MSData
whose source construction is retained by the nonblock assembly owner. -/
theorem MSData.joinCore_eq (d : MSData c n) (hn : 1 < n) :
    (K c ⊔ S c).pCoreIn 2 = Q c := by
  obtain ⟨A,hUA,hAQ,_,_,hA,_,_⟩ := d.exists_sylow_invariant_elementary_lift
  let a : invariantCoreLifts c := ⟨A,hUA,hAQ,le_sup_left.trans hA⟩
  rw [(d.joinCore_eq_core_sup_liftCentralizer hn a hA).1,
    d.joinCore_liftCentralizer_eq hn a hA]
  exact sup_eq_left.mpr hAQ.le

/-- C.1.35(4) on the original Sylow intersection: its two-rank is exactly 6n. -/
theorem MSData.sylow_primeRank (d : MSData c n) (hn : 1 < n) :
    primeRank 2 (S c) = 6*n := by
  obtain ⟨A,hUA,hAQ,hAe,hAc,hA,_,_⟩ := d.exists_sylow_invariant_elementary_lift
  let a : invariantCoreLifts c := ⟨A,hUA,hAQ,le_sup_left.trans hA⟩
  obtain ⟨E,hE,hout⟩ := d.exists_maxElementary_outside_joinCore
  have hec := (d.maxElementary_core_equality hn a hA E hE hout).2.1
  rw [d.joinCore_liftCentralizer_eq hn a hA] at hec
  have hEcard : Nat.card E = 2^(6*n) := hec.trans hAc
  apply le_antisymm
  · apply (primeRank_le_iff_elementary_card_le (S c)).mpr
    intro B hB
    let := hB
    have hh := hE.2.2 (B.map (S c).subtype) (map_subtype_le _) IsElementaryAbelian.map_subtype
    rwa [card_map_of_injective (S c).subtype_injective,hEcard] at hh
  · rw [←d.core_primeRank]
    exact primeRank_mono 2 (core_le_sylow c)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
