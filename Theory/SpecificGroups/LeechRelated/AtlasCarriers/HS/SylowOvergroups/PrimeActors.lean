module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Overgroups
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeNormalizerThreePart
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SolvableSylowOvergroups.OrderActors
public import Theory.SpecificGroups.SymmetricFive.NoForty

/-!
# Two-core sections and quintic actors in Higman–Sims

The certified full-Sylow cover has two actual local normalizers. Their
maps to S₅ and GL₃(2) have two-group kernels, so every subgroup section
modulo its intrinsic two-core has order dividing 840. This is used to
identify the right rank-one quotient in the original Cartan argument.

A three-free full-Sylow overgroup containing five would map to a subgroup
of order forty in S₅, which is impossible; the other local is five-free.
The actual outer two-group calculation then excludes a faithful quintic
actor on a normal HS factor with the original actor–Sylow order bound.

Source: Aschbacher–Smith A.3.12(18) and5.2.2, pp.47–48 and648–649.
The imported native certificates retain the ATLAS HSG1-p100B0 carrier,
permutation conventions, attribution and license. No new enumeration or
simplicity premise is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.HS.SylowOvergroups
open EvenLocalCandidates

private theorem conjugate_cover (S : Sylow 2 Carrier) (P : Subgroup Carrier)
    (hSP : (S : Subgroup Carrier) ≤ P) (hP : P ≠ ⊤) :
    ∃ c : Carrier ≃* Carrier,
      subgroup ≤ P.map c.toMonoidHom ∧
      (P.map c.toMonoidHom ≤ localGroup 0 ∨ P.map c.toMonoidHom ≤ localGroup 2) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Carrier S BlockNormalizer.baseSylow
  let c := MulAut.conj g
  have hS : (S : Subgroup Carrier).map c.toMonoidHom = subgroup :=
    congrArg Sylow.toSubgroup hg
  have hPc : P.map c.toMonoidHom ≠ ⊤ := by
    intro he
    apply hP
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [he,map_top_of_surjective _ c.surjective]
  exact ⟨c,hS ▸ map_mono hSP,proper_overgroup_le _ (hS ▸ map_mono hSP) hPc⟩

private theorem large_aut_card (i : Fin 3) : Nat.card (MulAut (elementary i)) ∣ 168 := by
  let := elementary_isElementaryAbelian i
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (elementary i)).exists_card_eq
  have hnle : n ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [←hn] using elementary_card_le_eight i
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow (elementary i) n hn]
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

private theorem large_kernel (i : Fin 3) (hi : i ≠ 0) :
    IsPGroup 2 (elementary i).normalizerMonoidHom.ker := by
  rw [normalizerMonoidHom_ker]
  exact (large_elementary_centralizer_isPGroup i hi).of_equiv
    (subgroupOfEquivOfLe (centralizer_le_normalizer (elementary i : Set Carrier))).symm

private theorem section_card_dvd {A Y : Type*} [Group A] [Finite A] [Group Y] [Finite Y]
    (f : A →* Y) (hk : IsPGroup 2 f.ker) (B : Subgroup A) :
    Nat.card (B ⧸ pCore 2 B) ∣ Nat.card Y := by
  have hkb : IsPGroup 2 (f.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  rw [Nat.card_congr ((f.subgroupMap B).pCoreQuotientEquiv
    (f.subgroupMap_surjective B) hkb).toEquiv]
  exact (card_quotient_dvd_card _).trans (B.map f).card_subgroup_dvd_card

/-- Any subgroup of a proper full-Sylow overgroup has its intrinsic two-core
quotient order dividing the least common multiple of 120 and 168. -/
theorem proper_overgroup_section_order (S : Sylow 2 Carrier) (J B : Subgroup Carrier)
    (hSJ : (S : Subgroup Carrier) ≤ J) (hJ : J ≠ ⊤) (hBJ : B ≤ J) :
    Nat.card (B ⧸ pCore 2 B) ∣ 840 := by
  obtain ⟨c,_,hc⟩ := conjugate_cover S J hSJ hJ
  let C := B.map c.toMonoidHom
  let e := c.subgroupMap B
  let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  rw [Nat.card_congr eQ.toEquiv]
  change Nat.card (C ⧸ pCore 2 C) ∣ 840
  have hC : C ≤ J.map c.toMonoidHom := map_mono hBJ
  rcases hc with hc | hc
  · let b := subgroupOfEquivOfLe (hC.trans hc)
    let bQ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
    rw [←Nat.card_congr bQ.toEquiv]
    apply (section_card_dvd CentralNormalizerThreePart.PairQuotient.fiveHom
      (by rw [CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]
          exact CentralInvolutionCore.core_isPGroup) _).trans
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  · let b := subgroupOfEquivOfLe (hC.trans hc)
    let bQ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
    rw [←Nat.card_congr bQ.toEquiv]
    exact (section_card_dvd (elementary 2).normalizerMonoidHom
      (large_kernel 2 (by decide)) _).trans ((large_aut_card 2).trans (by decide))

private theorem five_image {A Y : Type*} [Group A] [Finite A] [Group Y] [Finite Y]
    (f : A →* Y) (hk : IsPGroup 2 f.ker) (B : Subgroup A)
    (h5 : 5 ∣ Nat.card B) : 5 ∣ Nat.card (B.map f) := by
  let g := f.comp B.subtype
  have hkg : IsPGroup 2 g.ker := by
    change IsPGroup 2 (f.ker.subgroupOf B)
    exact hk.comap_subtype
  obtain ⟨a,ha⟩ := hkg.exists_card_eq
  have hcop : Nat.Coprime 5 (Nat.card g.ker) := by
    rw [ha]
    exact (by decide : Nat.Coprime 5 2).pow_right a
  have he := g.ker.card_mul_index
  rw [index_ker] at he
  rw [←he] at h5
  have hi := hcop.dvd_of_dvd_mul_left h5
  simpa only [g,MonoidHom.range_comp,range_subtype] using hi

/-- A three-free full-Sylow overgroup in HS has no factor five in its order. -/
theorem not_five_of_three_free (S : Sylow 2 Carrier) (J : Subgroup Carrier)
    (hSJ : (S : Subgroup Carrier) ≤ J) (h3 : ¬ 3 ∣ Nat.card J) :
    ¬ 5 ∣ Nat.card J := by
  have hJ : J ≠ ⊤ := by
    intro he
    apply h3
    rw [he,card_top,NormalizerIndex.card_carrier]
    decide
  obtain ⟨c,hsc,hc⟩ := conjugate_cover S J hSJ hJ
  let C := J.map c.toMonoidHom
  have he : Nat.card C = Nat.card J := card_map_of_injective c.injective
  intro h5
  rcases hc with hc | hc
  · let B := C.subgroupOf (localGroup 0)
    have hB : Nat.card B = Nat.card J :=
      (Nat.card_congr (subgroupOfEquivOfLe hc).toEquiv).trans he
    let f := CentralNormalizerThreePart.PairQuotient.fiveHom
    have hk : IsPGroup 2 f.ker := by
      rw [CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]
      exact CentralInvolutionCore.core_isPGroup
    let P := (BlockNormalizer.baseSylow.subtype (hsc.trans hc)).mapSurjective
      CentralNormalizerThreePart.PairQuotient.fiveHom_surjective
    have hPB : (P : Subgroup (Equiv.Perm (Fin 5))) ≤ B.map f := map_mono (comap_mono hsc)
    have h8 : 8 ∣ Nat.card (B.map f) := by
      have hp : Nat.card P = 8 := by
        rw [P.card_eq_multiplicity,Nat.card_eq_fintype_card,Fintype.card_perm]
        decide +kernel
      exact hp ▸ card_dvd_of_le hPB
    have hd : Nat.card (B.map f) ∣ 120 := by
      convert (B.map f).card_subgroup_dvd_card using 1
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    have h3b : ¬ 3 ∣ Nat.card (B.map f) := fun hh =>
      h3 (hB ▸ hh.trans (B.card_map_dvd f))
    have h5b := five_image f hk B (hB ▸ h5)
    have hcases : ∀ m ∈ (120 : ℕ).divisors,
        8 ∣ m → ¬ 3 ∣ m → 5 ∣ m → m = 40 := by decide +kernel
    exact _root_.SymmetricFive.subgroup_card_ne_forty _
      (hcases _ (Nat.mem_divisors.mpr ⟨hd,by decide⟩) h8 h3b h5b)
  · let B := C.subgroupOf (localGroup 2)
    have hB : Nat.card B = Nat.card J :=
      (Nat.card_congr (subgroupOfEquivOfLe hc).toEquiv).trans he
    have hd := (five_image (elementary 2).normalizerMonoidHom
      (large_kernel 2 (by decide)) B (hB ▸ h5)).trans
      ((B.map (elementary 2).normalizerMonoidHom).card_subgroup_dvd_card.trans (large_aut_card 2))
    norm_num at hd

variable {G : Type*} [Group G] [Finite G]
/-- A faithful quintic actor on a normal HS factor is incompatible with
the original actor-Sylow order bound. -/
theorem no_five_actor (K E : Subgroup G) [K.Normal] (S : Sylow 2 G) {a : ℕ}
    (e : K ≃* Carrier) (hE : Nat.card E = 5)
    (hd : Disjoint E (centralizer (K : Set G)))
    (hc : Nat.card (E ⊔ (S : Subgroup G) : Subgroup G) ∣ 2^a * 5) : False := by
  have hzK : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center Carrier at hh
    rw [BlockNormalizer.center_carrier_eq_bot,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hout := outer_isPGroup_two_of_pointStabilizer_map pointStabilizer_map
    normalizer_relIndex_dvd_two_pow
  apply no_odd_actor_of_sylow_order_bound K E S (by decide : Odd 5) hzK
    (hout.of_equiv (MulAut.outerCongr e).symm) _ hE hd hc
  intro P J hJ hPJ
  have h3 : ¬3 ∣ Nat.card J := Nat.prime_three.coprime_iff_not_dvd.mp
    ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right (by decide)).of_dvd_right hJ)
  have hh := not_five_of_three_free (P.mapSurjective e.surjective) (J.map e.toMonoidHom)
    (map_mono hPJ) (by rwa [card_map_of_injective e.injective])
  rwa [card_map_of_injective e.injective] at hh
end Sporadic.LeechRelated.HS.SylowOvergroups
