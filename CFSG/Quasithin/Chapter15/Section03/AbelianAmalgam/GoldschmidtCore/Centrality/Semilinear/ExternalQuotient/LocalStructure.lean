module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.SourceKernel
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.NormalizedSupCard

/-!
# External cubic group: intersections, relative cores and quotient factors

In the nontrivial character branch of the repaired 15.3.68 argument,
B=Y_E is external to H=G₀. Its cubic quotient forces B∩H=B₀; the
normal two-subgroups of B map trivially to that quotient. The kernel
intersection N is normal in B⊔H because [N,B]≤B₀≤N. Index three
promotes the supplied Sylow subgroup and identifies O₂(B⊔H)=N.
Relative normality, separately in H and G₁, gives the two local core
identities. The literal quotient character supplies compatible maps
Q/N≃C₂ and K/N≃H/Q.

The inputs B₀≤N follow from SourceKernel.terminal_kernel_reduction;
no containment B≤H or common-core equality is assumed.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1152–1155, repaired proof of 15.3.68(2). These are conditional group
theoretic steps, not an assertion of the printed common-core argument.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ExternalQuotient
variable {G : Type*} [Group G] [Finite G]

theorem aut_card (B : Subgroup G) (hc : Nat.card (B ⧸ localTwoCore B) = 3) :
    Nat.card (MulAut (B ⧸ localTwoCore B)) = 2 := by
  let := isCyclic_of_prime_card hc
  rw [IsCyclic.card_mulAut, hc]
  decide

noncomputable def autEquiv (B : Subgroup G) (hc : Nat.card (B ⧸ localTwoCore B) = 3) :
    MulAut (B ⧸ localTwoCore B) ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq (aut_card B hc) (by simp)

omit [Finite G] in
private theorem psubgroup_le_core (B A : Subgroup G)
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hA : IsPGroup 2 A) (hAB : A ≤ B) :
    A ≤ ambientTwoCore B := by
  let f := QuotientGroup.mk' (localTwoCore B)
  have hp : IsPGroup 2 ((A.subgroupOf B).map f) := hA.comap_subtype.map f
  have hp3 : IsPGroup 3 (B ⧸ localTwoCore B) := IsPGroup.of_card (hc.trans (pow_one 3).symm)
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ hp (hp3.to_subgroup ⊤)
  have he : (A.subgroupOf B).map f = ⊥ := disjoint_top.mp hd
  have hk : A.subgroupOf B ≤ localTwoCore B := by
    simpa [f] using (Subgroup.map_eq_bot_iff _).mp he
  intro a ha
  exact hk (show (⟨a,hAB ha⟩ : B) ∈ A.subgroupOf B from ha)

omit [Finite G] in
private theorem prime_section_dichotomy (B A : Subgroup G)
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (h0 : ambientTwoCore B ≤ A) :
    B ⊓ A = ambientTwoCore B ∨ B ≤ A := by
  let f := QuotientGroup.mk' (localTwoCore B)
  let : Fact (Nat.card (B ⧸ localTwoCore B)).Prime := ⟨hc ▸ Nat.prime_three⟩
  have hker : f.ker ≤ A.subgroupOf B := by
    rw [QuotientGroup.ker_mk']
    exact fun x hx => h0 hx
  rcases ((A.subgroupOf B).map f).eq_bot_or_eq_top_of_prime_card with hz | ht
  · left
    have hle : A.subgroupOf B ≤ localTwoCore B := by
      simpa [f] using (Subgroup.map_eq_bot_iff _).mp hz
    apply le_antisymm
    · intro x hx
      exact hle (show (⟨x,hx.1⟩ : B) ∈ A.subgroupOf B from hx.2)
    · exact le_inf (pCoreIn_le 2 B) h0
  · right
    have hall : A.subgroupOf B = ⊤ := by
      rw [← comap_map_eq_self hker, ht, comap_top]
    intro b hb
    exact show (⟨b,hb⟩ : B) ∈ A.subgroupOf B by rw [hall]; trivial

omit [Finite G] in
theorem external_intersection (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (h0 : ambientTwoCore B ≤ ambientTwoCore H)
    (hbad : ∃ q : ambientTwoCore H,
      quotientAction H B hHB ⟨q.1,pCoreIn_le 2 H q.2⟩ ≠ 1) :
    B ⊓ H = ambientTwoCore B := by
  rcases prime_section_dichotomy B H hc (h0.trans (pCoreIn_le 2 H)) with he | hBH
  · exact he
  · obtain ⟨q,hq⟩ := hbad
    apply False.elim
    apply hq
    have hQB : ambientTwoCore H ⊓ B ≤ ambientTwoCore B :=
      psubgroup_le_core B _ hc (isPGroup_pCoreIn 2 H).to_inf_left inf_le_right
    have hQnormal : H ≤ normalizer (ambientTwoCore H : Set G) :=
      H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    have hcomm : ⁅ambientTwoCore H, B⁆ ≤ ambientTwoCore B :=
      (le_inf (le_normalizer_iff_commutator_le_left.mp (hBH.trans hQnormal))
        (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 H).trans hHB))).trans hQB
    have hk := (mem_characterKernel_iff H B hHB q (pCoreIn_le 2 H q.2)).mpr
      (fun b hb => hcomm (commutator_mem_commutator q.2 hb))
    obtain ⟨x,hx,hxq⟩ := hk
    have hxe : x = ⟨q.1,pCoreIn_le 2 H q.2⟩ := Subtype.ext hxq
    exact hxe ▸ hx

omit [Finite G] in
private theorem core_normalized (A : Subgroup G) :
    A ≤ normalizer (ambientTwoCore A : Set G) :=
  A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))

omit [Finite G] in
private theorem core_inter_of_normalized (H A : Subgroup G)
    (hAH : A ≤ H) (hn : H ≤ normalizer (A : Set G)) :
    ambientTwoCore A = ambientTwoCore H ⊓ A := by
  apply le_antisymm
  · exact le_inf (pCoreIn_mono_of_normalizes hAH hn) (pCoreIn_le 2 A)
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H).to_inf_left inf_le_right
      ((le_inf (hAH.trans (core_normalized H)) A.le_normalizer).trans
        inf_normalizer_le_normalizer_inf)

omit [Finite G] in
theorem kernel_core (H B : Subgroup G) (hHB : H ≤ normalizer (B : Set G)) :
    ambientTwoCore (characterKernel H B hHB) =
      ambientTwoCore H ⊓ characterKernel H B hHB :=
  core_inter_of_normalized H _ (map_subtype_le _) (characterKernel_normalized H B hHB)

omit [Finite G] in
theorem first_kernel_core (H B G₁ R : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) (hG₁ : G₁ ≤ H)
    (hR : ambientTwoCore G₁ ⊓ characterKernel H B hHB = R) :
    ambientTwoCore (G₁ ⊓ characterKernel H B hHB) = R := by
  have hn : G₁ ≤ normalizer (G₁ ⊓ characterKernel H B hHB : Set G) :=
    (le_inf G₁.le_normalizer (hG₁.trans (characterKernel_normalized H B hHB))).trans
      inf_normalizer_le_normalizer_inf
  rw [core_inter_of_normalized G₁ _ inf_le_left hn, ← inf_assoc,
    inf_eq_left.mpr (show ambientTwoCore G₁ ≤ G₁ from pCoreIn_le 2 G₁), hR]

omit [Finite G] in
/-- The source identity B₀ ≤ C(U), N=C_H(U) supplies B₀ ≤ N. -/
theorem external_core_le_kernel_inter (H B U : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (h0 : ambientTwoCore B ≤ ambientTwoCore H)
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hN : ambientTwoCore H ⊓ characterKernel H B hHB = H ⊓ centralizer (U : Set G)) :
    ambientTwoCore B ≤ ambientTwoCore H ⊓ characterKernel H B hHB := by
  rw [hN]
  exact le_inf (h0.trans (pCoreIn_le 2 H)) h0U

omit [Finite G] in
theorem kernel_inter_normalized_join (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (h0N : ambientTwoCore B ≤ ambientTwoCore H ⊓ characterKernel H B hHB) :
    B ⊔ H ≤ normalizer (ambientTwoCore H ⊓ characterKernel H B hHB : Set G) := by
  apply sup_le
  · apply (le_normalizer_iff_commutator_le_left (H := B)
      (K := ambientTwoCore H ⊓ characterKernel H B hHB)).mpr
    apply (commutator_le.mpr ?_).trans h0N
    intro n hn b hb
    exact (mem_characterKernel_iff H B hHB n (pCoreIn_le 2 H hn.1)).mp hn.2 b hb
  · exact (le_inf (core_normalized H) (characterKernel_normalized H B hHB)).trans
      inf_normalizer_le_normalizer_inf

private theorem normalized_join_index (B H : Subgroup G)
    (hn : H ≤ normalizer (B : Set G)) : H.relIndex (B ⊔ H) = H.relIndex B := by
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes B H hn
  have hcH := relIndex_mul_relIndex (⊥ : Subgroup G) H (B ⊔ H) bot_le le_sup_right
  simp only [relIndex_bot_left] at hcH
  have hcB := relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ H) B bot_le inf_le_left
  simp only [relIndex_bot_left] at hcB
  have hc : Nat.card (B ⊓ H : Subgroup G) * Nat.card H * H.relIndex (B ⊔ H) =
      Nat.card (B ⊓ H : Subgroup G) * Nat.card H * H.relIndex B := by
    rw [mul_assoc, hcH, ← hmul, ← hcB, inf_relIndex_left]
    ac_rfl
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos Nat.card_pos Nat.card_pos) hc

theorem external_join_index (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hinter : B ⊓ H = ambientTwoCore B) : H.relIndex (B ⊔ H) = 3 := by
  rw [normalized_join_index B H hHB, ← inf_relIndex_left, hinter]
  exact hc

theorem sylow_in_external_join (H B S : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hinter : B ⊓ H = ambientTwoCore B)
    (hS : Chapter1.IsSylowIn 2 S H) : Chapter1.IsSylowIn 2 S (B ⊔ H) := by
  obtain ⟨T,hT⟩ := hS
  have hSH : S ≤ H := hT ▸ map_subtype_le _
  have hi : ¬ 2 ∣ S.relIndex (B ⊔ H) := by
    rw [← relIndex_mul_relIndex S H (B ⊔ H) hSH le_sup_right,
      external_join_index H B hHB hc hinter]
    apply Nat.Prime.not_dvd_mul Nat.prime_two _ (by decide)
    have he : S.subgroupOf H = (T : Subgroup H) := by rw [← hT, subgroupOf_map_subtype_eq]
    simpa only [relIndex, he] using T.not_dvd_index
  have hp : IsPGroup 2 (S.subgroupOf (B ⊔ H)) :=
    (hT ▸ T.isPGroup'.map H.subtype).comap_subtype
  exact ⟨hp.toSylow hi, map_subgroupOf_eq_of_le (hSH.trans le_sup_right)⟩

theorem kernel_sylow (H B S : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) (hS : Chapter1.IsSylowIn 2 S H) :
    Chapter1.IsSylowIn 2 (S ⊓ characterKernel H B hHB) (characterKernel H B hHB) := by
  obtain ⟨T,hT⟩ := hS
  let K := characterKernel H B hHB
  have hKH : K ≤ H := map_subtype_le _
  let : (K.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (characterKernel_normalized H B hHB)
  obtain ⟨U,hU⟩ := T.exists_subgroupOf_eq_of_normal (K.subgroupOf H)
  let e := subgroupOfEquivOfLe hKH
  refine ⟨U.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((U : Subgroup (K.subgroupOf H)).map e.toMonoidHom).map K.subtype = _
  rw [hU, map_map]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨hT ▸ mem_map.mpr ⟨y.1,hy,rfl⟩,y.2⟩
  · rintro ⟨hxS,hxK⟩
    obtain ⟨t,ht,he⟩ := mem_map.mp (hT.symm ▸ hxS)
    change (t : G) = x at he
    have htK : (t : G) ∈ K := he.symm ▸ hxK
    exact ⟨⟨t,htK⟩,ht,he⟩


theorem external_join_core (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hinter : B ⊓ H = ambientTwoCore B)
    (h0N : ambientTwoCore B ≤ ambientTwoCore H ⊓ characterKernel H B hHB) :
    ambientTwoCore (B ⊔ H) = ambientTwoCore H ⊓ characterKernel H B hHB := by
  let L := B ⊔ H
  let N := ambientTwoCore H ⊓ characterKernel H B hHB
  have hNH : N ≤ H := inf_le_left.trans (pCoreIn_le 2 H)
  have hNL : N ≤ L := hNH.trans le_sup_right
  have hn := kernel_inter_normalized_join H B hHB h0N
  apply le_antisymm
  · let S : Sylow 2 H := Sylow.nonempty.some
    obtain ⟨T,hT⟩ := sylow_in_external_join H B ((S : Subgroup H).map H.subtype)
      hHB hc hinter ⟨S,rfl⟩
    have hcoreH : ambientTwoCore L ≤ H := by
      have hle := pCoreIn_le_sylow L T
      rw [hT] at hle
      exact hle.trans (map_subtype_le _)
    have hcoreQ : ambientTwoCore L ≤ ambientTwoCore H :=
      le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L) hcoreH
        (le_sup_right.trans (core_normalized L))
    have hCB : ambientTwoCore L ⊓ B ≤ ambientTwoCore B :=
      psubgroup_le_core B _ hc (isPGroup_pCoreIn 2 L).to_inf_left inf_le_right
    have hcomm : ⁅ambientTwoCore L, B⁆ ≤ ambientTwoCore B :=
      (le_inf (le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans (core_normalized L)))
        (le_normalizer_iff_commutator_le_right.mp
          ((pCoreIn_le 2 L).trans (sup_le B.le_normalizer hHB)))).trans hCB
    exact le_inf hcoreQ (fun x hx => (mem_characterKernel_iff H B hHB x (hcoreH hx)).mpr
      (fun b hb => hcomm (commutator_mem_commutator hx hb)))
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H).to_inf_left hNL hn


noncomputable abbrev kernelIntersection (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) : Subgroup G :=
  ambientTwoCore H ⊓ characterKernel H B hHB

omit [Finite G] in
private theorem kernelIntersection_normalized (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) :
    H ≤ normalizer (kernelIntersection H B hHB : Set G) :=
  (le_inf (core_normalized H) (characterKernel_normalized H B hHB)).trans
    inf_normalizer_le_normalizer_inf

instance core_inter_normal (H B : Subgroup G) (hHB : H ≤ normalizer (B : Set G)) :
    ((kernelIntersection H B hHB).subgroupOf (ambientTwoCore H)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 H).trans (kernelIntersection_normalized H B hHB))

instance kernel_inter_normal (H B : Subgroup G) (hHB : H ≤ normalizer (B : Set G)) :
    ((kernelIntersection H B hHB).subgroupOf (characterKernel H B hHB)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((map_subtype_le _).trans (kernelIntersection_normalized H B hHB))

noncomputable def coreCharacter (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) :
    ambientTwoCore H →* MulAut (B ⧸ localTwoCore B) :=
  (quotientAction H B hHB).comp (inclusion (pCoreIn_le 2 H))

omit [Finite G] in
theorem coreCharacter_ker (H B : Subgroup G) (hHB : H ≤ normalizer (B : Set G)) :
    (coreCharacter H B hHB).ker =
      (kernelIntersection H B hHB).subgroupOf (ambientTwoCore H) := by
  ext q
  change quotientAction H B hHB ⟨q.1,pCoreIn_le 2 H q.2⟩ = 1 ↔
    q.1 ∈ ambientTwoCore H ∧ q.1 ∈ characterKernel H B hHB
  constructor
  · intro hq
    exact ⟨q.2,mem_map.mpr ⟨⟨q.1,pCoreIn_le 2 H q.2⟩,hq,rfl⟩⟩
  · rintro ⟨_,x,hx,he⟩
    have he' : x = ⟨q.1,pCoreIn_le 2 H q.2⟩ := Subtype.ext he
    exact he' ▸ hx

theorem coreCharacter_surjective (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hbad : ∃ q : ambientTwoCore H, coreCharacter H B hHB q ≠ 1) :
    Function.Surjective (coreCharacter H B hHB) := by
  let : Fact (Nat.card (MulAut (B ⧸ localTwoCore B))).Prime :=
    ⟨(aut_card B hc).symm ▸ Nat.prime_two⟩
  apply MonoidHom.range_eq_top.mp
  rcases (coreCharacter H B hHB).range.eq_bot_or_eq_top_of_prime_card with hz | ht
  · obtain ⟨q,hq⟩ := hbad
    exact (hq (show coreCharacter H B hHB q ∈ (⊥ : Subgroup _) from
      hz ▸ (show coreCharacter H B hHB q ∈ (coreCharacter H B hHB).range from ⟨q,rfl⟩))).elim
  · exact ht

noncomputable def coreQuotientEquiv (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hbad : ∃ q : ambientTwoCore H, coreCharacter H B hHB q ≠ 1) :
    (ambientTwoCore H ⧸ (kernelIntersection H B hHB).subgroupOf (ambientTwoCore H)) ≃*
      Multiplicative (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (coreCharacter_ker H B hHB).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (coreCharacter H B hHB)
      (coreCharacter_surjective H B hHB hc hbad)).trans (autEquiv B hc))

theorem coreQuotientEquiv_mk (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hbad : ∃ q : ambientTwoCore H, coreCharacter H B hHB q ≠ 1)
    (q : ambientTwoCore H) :
    coreQuotientEquiv H B hHB hc hbad (QuotientGroup.mk' _ q) =
      autEquiv B hc (coreCharacter H B hHB q) := by
  rfl

noncomputable def kernelToCoreQuotient (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) :
    characterKernel H B hHB →* (H ⧸ localTwoCore H) :=
  (QuotientGroup.mk' (localTwoCore H)).comp (inclusion (map_subtype_le _))

omit [Finite G] in
theorem kernelToCoreQuotient_ker (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) :
    (kernelToCoreQuotient H B hHB).ker =
      (kernelIntersection H B hHB).subgroupOf (characterKernel H B hHB) := by
  ext k
  change QuotientGroup.mk' (localTwoCore H) (inclusion (map_subtype_le _) k) = 1 ↔ _
  simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact ⟨fun hk => ⟨hk,k.2⟩,fun hk => hk.1⟩

theorem kernelToCoreQuotient_surjective (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hbad : ∃ q : ambientTwoCore H, coreCharacter H B hHB q ≠ 1) :
    Function.Surjective (kernelToCoreQuotient H B hHB) := by
  intro z
  obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (localTwoCore H) z
  obtain ⟨q,hq⟩ := coreCharacter_surjective H B hHB hc hbad (quotientAction H B hHB h)
  let qH : H := ⟨q.1,pCoreIn_le 2 H q.2⟩
  have hk : qH⁻¹ * h ∈ (quotientAction H B hHB).ker := by
    change quotientAction H B hHB (qH⁻¹ * h) = 1
    rw [map_mul,map_inv,show quotientAction H B hHB qH = quotientAction H B hHB h from hq,
      inv_mul_cancel]
  let k : characterKernel H B hHB := ⟨(qH⁻¹ * h : H),mem_map.mpr ⟨qH⁻¹ * h,hk,rfl⟩⟩
  refine ⟨k,?_⟩
  change QuotientGroup.mk' (localTwoCore H) (qH⁻¹ * h) = _
  rw [map_mul,map_inv,show QuotientGroup.mk' (localTwoCore H) qH = 1 from
    (QuotientGroup.eq_one_iff qH).mpr q.2,inv_one,one_mul]

noncomputable def kernelQuotientEquiv (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hbad : ∃ q : ambientTwoCore H, coreCharacter H B hHB q ≠ 1) :
    (characterKernel H B hHB ⧸
      (kernelIntersection H B hHB).subgroupOf (characterKernel H B hHB)) ≃*
        (H ⧸ localTwoCore H) :=
  (QuotientGroup.quotientMulEquivOfEq (kernelToCoreQuotient_ker H B hHB).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (kernelToCoreQuotient H B hHB)
      (kernelToCoreQuotient_surjective H B hHB hc hbad))

theorem kernelQuotientEquiv_mk (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hbad : ∃ q : ambientTwoCore H, coreCharacter H B hHB q ≠ 1)
    (k : characterKernel H B hHB) :
    kernelQuotientEquiv H B hHB hc hbad (QuotientGroup.mk' _ k) =
      kernelToCoreQuotient H B hHB k := by
  rfl

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ExternalQuotient
