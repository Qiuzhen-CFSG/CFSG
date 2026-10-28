module

public import Stellmacher.MainDefs
public import Stellmacher.SectionEleven.MultipleMaximalTwoRank
public import BenderSuzuki.SE.Final
public import FeitThompson.BGsection1.CentralizerLemmas

/-!
# Strong embedding is incompatible with the theorem-one local hypotheses

The Baumann-local hypothesis of Stellmacher's Theorem 1, together with two
maximal two-locals over the prescribed Sylow subgroup, excludes a strongly
embedded subgroup. The hypothesis is used only for two-locals containing that
Sylow, and the conclusion is the final field needed by Hypothesis 1.

The rank-one reduction is imported: two distinct maximal locals force a
four-group in the involution core. If a strongly embedded subgroup existed,
its global involution fusion would reduce every odd-core involution centralizer
to the centralizer of a central Sylow involution. That centralizer is a
characteristic-two local, so its odd core is trivial. Coprime four-group fixed
point generation then kills the ambient odd core.

The proved Bender--Suzuki Theorem SE now makes the involution core of the
strongly embedded subgroup a nontrivial two-group, via the normal Sylow of its
Borel image in the ambient involution-core quotient. Its normalizer is exactly
the strongly embedded subgroup, which is therefore itself two-local. Every
two-local over the original Sylow is contained in it; maximality would make
the two prescribed maximal locals equal.

Source: the Hypothesis-1 reduction asserted in Section 11 of
`refs/latex/stellmacher-n-group.tex`; the strong-embedding recognition and Borel
facts are the checked results in `BenderSuzuki.SE.Final` and
`BenderSuzuki.SE.Theorem4Induction`. No simplicity or global local-solvability
hypothesis is added.
-/

namespace Stellmacher.SectionEleven

open BenderSuzuki BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1
open scoped IsMulCommutative

private theorem normalizer_le_centralizer_of_card_two
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) (hK : Nat.card K = 2) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer (K : Set G) := by
  obtain ⟨t, ht_ne, ht_unique⟩ := (Nat.card_eq_two_iff' (1 : K)).mp hK
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  by_cases h1 : k = 1
  · simp [h1]
  have hkt : (⟨k, hk⟩ : K) = t := ht_unique ⟨k, hk⟩ (by
    intro he
    exact h1 (congrArg Subtype.val he))
  have hc : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg k).mp hk
  have hc1 : g * k * g⁻¹ ≠ 1 := by
    intro he
    have he' := congrArg (fun x : G => g⁻¹ * x * g) he
    exact h1 (by simpa [mul_assoc] using he')
  have hct : (⟨g * k * g⁻¹, hc⟩ : K) = t := ht_unique ⟨_, hc⟩ (by
    intro he
    exact hc1 (congrArg Subtype.val he))
  have he := congrArg (fun x : K => (x : G) * g) (hct.trans hkt.symm)
  simpa [mul_assoc] using he.symm

private theorem centralizer_isTwoLocal_of_involution
    {H : Type*} [Group H] [Finite H] {t : H}
    (ht : BenderSuzuki.PFAppendixIII.IsInvolution t) :
    IsTwoLocal (Subgroup.centralizer ({t} : Set H)) := by
  have hcard : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ht.2 ht.1
  refine ⟨Subgroup.zpowers t, by simpa using ht.1,
    isPGroup_zpowers_of_involution ht, ?_⟩
  have heq : Subgroup.centralizer ({t} : Set H) =
      Subgroup.centralizer (Subgroup.zpowers t : Set H) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [heq]
  exact le_antisymm (Subgroup.centralizer_le_normalizer _)
    (normalizer_le_centralizer_of_card_two _ hcard)

private theorem oddCore_comap_eq_bot_of_characteristicTwo
    {H : Type*} [Group H] [Finite H] (U : Subgroup H)
    (hchar : IsCharacteristicTwoType U) :
    (pPrimeCore 2 H).comap U.subtype = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : pPrimeCore 2 U = ⊥ := by
    have hle : pPrimeCore 2 U ≤ pCore 2 U :=
      (pPrimeCore_le_centralizer_of_normal_pgroup 2 (pCore 2 U)
        (pCore_isPGroup (p := 2) (G := U))).trans hchar
    obtain ⟨power, hpower⟩ := (pCore_isPGroup (p := 2) (G := U)).exists_card_eq
    have hcop : Nat.Coprime (Nat.card (pCore 2 U)) (Nat.card (pPrimeCore 2 U)) := by
      rw [hpower]
      exact (pPrimeCore_coprime_card (p := 2) (G := U)).pow_left power
    exact le_bot_iff.mp ((le_inf hle le_rfl).trans_eq
      (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot)
  have hinter : (pPrimeCore 2 H).comap U.subtype ≤ pPrimeCore 2 U := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ U.subtype_injective)
      (pPrimeCore_coprime_card (p := 2) (G := H))
  exact le_bot_iff.mp (hinter.trans_eq hodd)

private theorem exists_central_involution_of_sylow_nontrivial
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (hSne : (S : Subgroup H) ≠ ⊥) :
    ∃ t : H, BenderSuzuki.PFAppendixIII.IsInvolution t ∧
      (S : Subgroup H) ≤ Subgroup.centralizer ({t} : Set H) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot (S : Subgroup H)).mpr hSne
  let : Nontrivial (Subgroup.center S) := S.isPGroup'.center_nontrivial
  obtain ⟨n, hn, hcard⟩ :=
    (S.isPGroup'.to_subgroup (Subgroup.center S)).nontrivial_iff_card.mp inferInstance
  have hdiv : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2 hdiv
  have hzH : orderOf ((z : S) : H) = 2 := by
    simp only [Subgroup.orderOf_coe]
    exact hz
  have hinv : BenderSuzuki.PFAppendixIII.IsInvolution ((z : S) : H) :=
    ⟨(orderOf_eq_prime_iff.mp hzH).2, (orderOf_eq_prime_iff.mp hzH).1⟩
  refine ⟨((z : S) : H), hinv, ?_⟩
  intro x hx
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property ⟨x, hx⟩)

private theorem oddCore_involution_centralizer_eq_bot
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (hSne : (S : Subgroup H) ≠ ⊥)
    (hlocal : ∀ U : Subgroup H, IsTwoLocal U → (S : Subgroup H) ≤ U →
      IsCharacteristicTwoType U)
    {M : Subgroup H} (hM : BenderSuzuki.IsStronglyEmbedded M)
    {t : H} (ht : BenderSuzuki.PFAppendixIII.IsInvolution t) :
    pPrimeCore 2 H ⊓ Subgroup.centralizer ({t} : Set H) = ⊥ := by
  obtain ⟨z, hz, hSz⟩ := exists_central_involution_of_sylow_nontrivial S hSne
  have hchar := hlocal _ (centralizer_isTwoLocal_of_involution hz) hSz
  have hodd := oddCore_comap_eq_bot_of_characteristicTwo _ hchar
  obtain ⟨g, hg⟩ := hM.involutions_conjugate ht hz
  apply le_bot_iff.mp
  intro x hx
  have hxconj : g⁻¹ * x * g ∈ pPrimeCore 2 H := by
    simpa using (inferInstance : (pPrimeCore 2 H).Normal).conj_mem x hx.1 g⁻¹
  have hcomm : (g⁻¹ * x * g) * z = z * (g⁻¹ * x * g) := by
    rw [← hg]
    dsimp [rightConjugateElem]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    simpa [mul_assoc] using congrArg (fun y : H => g⁻¹ * y * g) hc
  have hmem : (⟨g⁻¹ * x * g, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩ :
      Subgroup.centralizer ({z} : Set H)) ∈
      (pPrimeCore 2 H).comap (Subgroup.centralizer ({z} : Set H)).subtype := hxconj
  rw [hodd] at hmem
  have he : g⁻¹ * x * g = 1 := congrArg Subtype.val hmem
  simpa [mul_assoc] using congrArg (fun y : H => g * y * g⁻¹) he

private theorem oddCore_eq_bot_of_strong_embedding_and_local
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (hSne : (S : Subgroup H) ≠ ⊥)
    (hlocal : ∀ U : Subgroup H, IsTwoLocal U → (S : Subgroup H) ≤ U →
      IsCharacteristicTwoType U)
    {M : Subgroup H} (hM : BenderSuzuki.IsStronglyEmbedded M)
    (hrank : TwoRankAtLeastTwo H) : pPrimeCore 2 H = ⊥ := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hUcard, hUsq⟩ := TwoRankAtLeastTwo.exists_subgroup hrank
  let W := pPrimeCore 2 H
  let : IsMulCommutative U := isMulCommutative_of_forall_sq_one hUsq
  let : CommGroup U := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 U) := ⟨IsPGroup.of_card (by norm_num [hUcard] : Nat.card U = 2 ^ 2)⟩
  have hUnormW : U ≤ Subgroup.normalizer W := by
    change U ≤ Subgroup.normalizer (pPrimeCore 2 H)
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  let : Subgroup.Normalizes U W := ⟨hUnormW⟩
  have hUnoncyclic : ¬ IsCyclic U := by
    intro hcyc
    obtain ⟨a, ha⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := U)).mp hcyc
    have hdvd := orderOf_dvd_iff_pow_eq_one.mpr (hUsq a)
    rw [ha, hUcard] at hdvd
    norm_num at hdvd
  have hgen : (⨆ (u : U) (_ : u ≠ 1),
      fixedPointSubgroup (↥(Subgroup.zpowers u)) W) = ⊤ :=
    proposition_1_16_a (G := W) (A := U) 2
      (pPrimeCore_coprime_card (p := 2) (G := H)) hUnoncyclic
  have hfix : ∀ (u : U), u ≠ 1 →
      fixedPointSubgroup (↥(Subgroup.zpowers u)) W = ⊥ := by
    intro u hu
    have hinv : BenderSuzuki.PFAppendixIII.IsInvolution (u : H) := by
      refine ⟨fun hone => hu (Subtype.ext hone), ?_⟩
      exact congrArg Subtype.val (hUsq u)
    have hcent := oddCore_involution_centralizer_eq_bot S hSne hlocal hM hinv
    have hfixeq : fixedPointSubgroup (↥(Subgroup.zpowers u)) W =
        (elementCentralizerIn W (u : H)).subgroupOf W := by
      exact fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn W U hUnormW u
    rw [hfixeq]
    change (W ⊓ Subgroup.centralizer ({(u : H)} : Set H)).subgroupOf W = ⊥
    rw [hcent]
    exact Subgroup.bot_subgroupOf W
  have htopbot : (⊤ : Subgroup W) = ⊥ := by
    rw [← hgen]
    exact iSup_eq_bot.mpr fun u => iSup_eq_bot.mpr fun hu => hfix u hu
  apply le_bot_iff.mp
  intro x hx
  have hxbot : (⟨x, hx⟩ : W) ∈ (⊥ : Subgroup W) := htopbot ▸ Subgroup.mem_top _
  exact congrArg Subtype.val hxbot

private theorem involutionCore_isPGroup_of_strong_embedding_of_oddCore_eq_bot
    {H : Type*} [Group H] [Finite H]
    {M : Subgroup H} (hM : BenderSuzuki.IsStronglyEmbedded M)
    (hrank : TwoRankAtLeastTwo (involutionCore H))
    (hodd : pPrimeCore 2 H = ⊥) : IsPGroup 2 (involutionCore M) := by
  let L : Subgroup H := involutionCore H
  have hcoreML : (involutionCore M).map M.subtype ≤ L := by
    rw [involutionCore_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro x ⟨y, hy, rfl⟩
    apply Subgroup.subset_closure
    exact IsInvolution.map_of_injective hy M.subtype Subtype.val_injective
  have hrankM : TwoRankAtLeastTwo (involutionCore M) :=
    rank_involutionCore_of_ambient_rank hM hrank
  have hrankML : TwoRankAtLeastTwo (M.comap L.subtype) :=
    theorem4bProposition63_twoRank_comap hrankM hcoreML
  have hLcore : L = (involutionCore L).map L.subtype := by
    rw [show involutionCore L = ⊤ from involutionCore_involutionCore_eq_top H]
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := L)).symm
  have himage := theorem4bProposition63_II4b_image_isPGroup
    (theorem_SE _ hM.comap_involutionCore) hLcore hrankML hcoreML
  have hoddL : twoPrimeCore L = ⊥ := by
    have hmap : (pPrimeCore 2 L).map L.subtype ≤ pPrimeCore 2 H :=
      pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 L
    apply (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp
    exact le_bot_iff.mp (hmap.trans_eq hodd)
  let f := theorem4bProposition63CoreQuotientMap hcoreML
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    rw [show f x = QuotientGroup.mk' (twoPrimeCore L)
      ⟨((x : M) : H), hcoreML (Subgroup.mem_map_of_mem M.subtype x.property)⟩ from
      theorem4bProposition63CoreQuotientMap_apply hcoreML x] at hx
    have hxcore : (⟨((x : M) : H), hcoreML
        (Subgroup.mem_map_of_mem M.subtype x.property)⟩ : L) ∈ twoPrimeCore L :=
      (QuotientGroup.eq_one_iff (N := twoPrimeCore L) _).mp hx
    rw [hoddL] at hxcore
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : L => (y : H)) (show (⟨((x : M) : H), hcoreML
      (Subgroup.mem_map_of_mem M.subtype x.property)⟩ : L) = 1 from hxcore)
  exact himage.of_injective f.rangeRestrict (fun x y heq => hf (congrArg Subtype.val heq))

private theorem normalizer_le_stronglyEmbedded
    {H : Type*} [Group H] [Finite H] {M Q : Subgroup H}
    (hM : BenderSuzuki.IsStronglyEmbedded M)
    (hQM : Q ≤ M) (hq : ∃ x : H, x ∈ Q ∧ BenderSuzuki.PFAppendixIII.IsInvolution x) :
    Subgroup.normalizer (Q : Set H) ≤ M := by
  obtain ⟨x, hxQ, hx⟩ := hq
  intro g hg
  have hgx : g * x * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hg x).mp hxQ
  apply hM.mem_of_involution_mem_rightConjugate (hQM hxQ) _ hx
  have hm := rightConjugateElem_mem_rightConjugate (M := M)
    (x := g * x * g⁻¹) (g := g) (hQM hgx)
  simpa [rightConjugateElem, mul_assoc] using hm

private theorem stronglyEmbedded_isTwoLocal_of_oddCore_eq_bot
    {H : Type*} [Group H] [Finite H]
    {M : Subgroup H} (hM : BenderSuzuki.IsStronglyEmbedded M)
    (hrank : TwoRankAtLeastTwo (involutionCore H))
    (hodd : pPrimeCore 2 H = ⊥) : IsTwoLocal M := by
  let Q : Subgroup H := (involutionCore M).map M.subtype
  have hQp : IsPGroup 2 Q :=
    (involutionCore_isPGroup_of_strong_embedding_of_oddCore_eq_bot hM hrank hodd).map M.subtype
  have hQM : Q ≤ M := Subgroup.map_subtype_le _
  obtain ⟨t, htM, ht⟩ := hM.exists_involution
  have htQ : t ∈ Q := by
    refine ⟨⟨t, htM⟩, ?_, rfl⟩
    exact Subgroup.subset_closure (IsInvolution.subtype ht htM)
  have hQne : Q ≠ ⊥ := by
    intro hbot
    exact ht.1 (by simpa [hbot] using htQ)
  have hQnormal : (Q.subgroupOf M).Normal := by
    have heq : Q.subgroupOf M = involutionCore M := by
      exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    rw [heq]
    infer_instance
  refine ⟨Q, hQne, hQp, le_antisymm ?_ ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mp hQnormal
  · exact normalizer_le_stronglyEmbedded hM hQM ⟨t, htQ, ht⟩

private theorem exists_stronglyEmbedded_over_sylow
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    {M : Subgroup H} (hM : BenderSuzuki.IsStronglyEmbedded M) :
    ∃ N : Subgroup H, BenderSuzuki.IsStronglyEmbedded N ∧ (S : Subgroup H) ≤ N := by
  classical
  obtain ⟨T, hTM⟩ := hM.containsSylowTwo
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S T
  let f : H ≃* H := MulAut.conj g
  let N := M.comap f.toMonoidHom
  have hNS : (S : Subgroup H) ≤ N := by
    intro x hx
    apply hTM
    have hle : f x ∈ ((g • S : Sylow 2 H) : Subgroup H) := by
      change f x ∈ (S : Subgroup H).map f.toMonoidHom
      exact Subgroup.mem_map_of_mem f.toMonoidHom hx
    simpa [hg] using hle
  refine ⟨N, ?_, hNS⟩
  apply hM.comap_of_injective f.toMonoidHom f.injective
  · intro htop
    apply hM.ne_top
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := f.surjective x
    have hy : y ∈ N := by
      change y ∈ M.comap f.toMonoidHom
      rw [htop]
      exact Subgroup.mem_top y
    exact hy
  · obtain ⟨t, htM, ht⟩ := hM.exists_involution
    refine ⟨f.symm t, ?_, IsInvolution.map_of_injective ht f.symm.toMonoidHom f.symm.injective⟩
    change f (f.symm t) ∈ M
    simpa using htM

private theorem twoLocal_le_stronglyEmbedded_of_sylow_le
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    {M P : Subgroup H} (hM : BenderSuzuki.IsStronglyEmbedded M)
    (hSM : (S : Subgroup H) ≤ M)
    (hP : IsTwoLocal P) (hSP : (S : Subgroup H) ≤ P) : P ≤ M := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQne, hQp, hP⟩ := hP
  have hQP : Q ≤ P := hP ▸ Subgroup.le_normalizer
  let : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hP.le
  have hQsubp : IsPGroup 2 (Q.subgroupOf P) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hQsubS := hQsubp.le_sylow_of_normal (S.subtype hSP)
  have hQS : Q ≤ (S : Subgroup H) := by
    intro x hx
    exact hQsubS (show (⟨x, hQP hx⟩ : P) ∈ Q.subgroupOf P from hx)
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  obtain ⟨n, hn, hcard⟩ := hQp.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card Q := by
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 hdvd
  have htH : orderOf (t : H) = 2 := by simpa only [Subgroup.orderOf_coe] using ht
  rw [hP]
  apply normalizer_le_stronglyEmbedded hM (hQS.trans hSM)
  exact ⟨t, t.property, (orderOf_eq_prime_iff.mp htH).2, (orderOf_eq_prime_iff.mp htH).1⟩

private theorem no_strongly_embedded_of_local_multiple_rank
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (hSne : (S : Subgroup H) ≠ ⊥)
    (hlocal : ∀ U : Subgroup H, IsTwoLocal U → (S : Subgroup H) ≤ U →
      IsCharacteristicTwoType U)
    (hrank : TwoRankAtLeastTwo (involutionCore H))
    (hmax : ∃ P1 P2 : Subgroup H,
      P1 ≠ P2 ∧ IsMaximalTwoLocal P1 ∧ IsMaximalTwoLocal P2 ∧
      (S : Subgroup H) ≤ P1 ∧ (S : Subgroup H) ≤ P2) :
    ¬ ∃ M : Subgroup H, _root_.IsStronglyEmbedded M := by
  rintro ⟨M, hM⟩
  have hMB : BenderSuzuki.IsStronglyEmbedded M := by
    refine ⟨hM.1, hM.2.1, ?_⟩
    intro g hg x hxM hxright
    have hginv : g⁻¹ ∉ M := fun hi => hg (by simpa using M.inv_mem hi)
    apply hM.2.2 g⁻¹ hginv x
    refine ⟨hxM, ?_⟩
    simpa [rightConjugate, Subgroup.conjBy] using hxright
  obtain ⟨N, hN, hSN⟩ := exists_stronglyEmbedded_over_sylow S hMB
  have hodd : pPrimeCore 2 H = ⊥ :=
    oddCore_eq_bot_of_strong_embedding_and_local S hSne hlocal hN
      (hrank.map_of_injective (involutionCore H).subtype Subtype.val_injective)
  have hNlocal := stronglyEmbedded_isTwoLocal_of_oddCore_eq_bot hN hrank hodd
  obtain ⟨P1, P2, hne, hP1, hP2, hSP1, hSP2⟩ := hmax
  have hP1N := twoLocal_le_stronglyEmbedded_of_sylow_le S hN hSN hP1.prop hSP1
  have hP2N := twoLocal_le_stronglyEmbedded_of_sylow_le S hN hSN hP2.prop hSP2
  exact hne ((hP1N.antisymm (hP1.2 hNlocal hP1N)).trans
    (hP2N.antisymm (hP2.2 hNlocal hP2N)).symm)

/-- The original theorem-one local assumptions exclude a strongly embedded
subgroup, with the prescribed Sylow subgroup unchanged. -/
public theorem no_strongly_embedded_of_theorem_one_hypotheses
    {H : Type*} [Group H] [Finite H] (S0 : Sylow 2 H)
    (hlocal : ∀ U : Subgroup H,
      IsTwoLocal U → baumannSubgroup S0 ≤ U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hmax : ∃ P1 P2 : Subgroup H,
      P1 ≠ P2 ∧ IsMaximalTwoLocal P1 ∧ IsMaximalTwoLocal P2 ∧
      (S0 : Subgroup H) ≤ P1 ∧ (S0 : Subgroup H) ≤ P2) :
    ¬ ∃ M : Subgroup H, _root_.IsStronglyEmbedded M := by
  have hSne : (S0 : Subgroup H) ≠ ⊥ := by
    obtain ⟨P1, P2, hne, hP1, hP2, hS1, hS2⟩ := hmax
    obtain ⟨Q, hQne, hQp, _⟩ := hP1.prop
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
    obtain ⟨n, hn, hcard⟩ := hQp.nontrivial_iff_card.mp inferInstance
    have hdvd : 2 ∣ Nat.card H := by
      apply dvd_trans (b := Nat.card Q) _ Q.card_subgroup_dvd_card
      rw [hcard]
      exact dvd_pow_self 2 hn.ne'
    exact S0.ne_bot_of_dvd_card hdvd
  apply no_strongly_embedded_of_local_multiple_rank S0 hSne _
    (involutionCore_twoRank_of_multiple_maximal S0 hmax) hmax
  intro U hU hSU
  exact (hlocal U hU ((show baumannSubgroup S0 ≤ (S0 : Subgroup H) from
    inf_le_left).trans hSU)).2

end Stellmacher.SectionEleven
