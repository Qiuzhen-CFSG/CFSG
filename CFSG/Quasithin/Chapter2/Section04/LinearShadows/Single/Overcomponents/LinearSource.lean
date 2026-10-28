module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Overcomponents.SmallSource
public import Theory.SpecificGroups.PSL3Four.CentralCover.OppositeCenter
/-!
# Excluding the original PSL₃(4) overcomponent

The original block determines the field degree, the central four-group, both
elementary cores and the common Sylow order. Concrete full-plane normalizers
force equal centers for the block and its conjugate by the original outside
element. The source 2.4.4 normalizer barrier excludes that equality.
Source: Aschbacher–Smith 2.4.11, printed p.532.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]
lemma source_overcomponent_not_psl_three_four
    {M : Subgroup G} (d : MinimalBlockSetup M)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ J : Subgroup G, IsMaximalTwoLocal J → (T : Subgroup G) ≤ J → J = M)
    (hZ : center (d.block.map d.H.subtype) ≠ ⊥)
    (K : Subgroup G) [Group.IsPerfect K] (hLK : d.block.map d.H.subtype ≤ K)
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (hZK : (center K).map K.subtype ≤
      (center (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype) : False := by
  let L := d.block.map d.H.subtype
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Q := sourceModule L
  let Z := (center L).map L.subtype
  have h := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hc := source_block_core_eq_module d hG T hST hsingle
  obtain ⟨_,D,_,_,_,x,hxT,hxS,_,hz⟩ :=
    source_center_torus_and_splitting d hG T hST hsingle hL hM hTM hunique
  have hzcard : Nat.card (center L) = 2^n := (hz.resolve_left hZ).1
  have hZKi : center K ≤ (center L).map (inclusion hLK) := by
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [Subgroup.map_map]
    exact hZK
  obtain ⟨hn,hcenter⟩ := Overcomponents.center_eq_map_of_psl_three_four h hc hzcard
    (inclusion hLK) (inclusion_injective hLK) e hZKi
  have hZeq : (center K).map K.subtype = Z := by
    rw [hcenter,Subgroup.map_map]
    rfl
  have hZc : Nat.card (center K) = 4 := by
    rw [hcenter,card_map_of_injective (inclusion_injective hLK),hzcard,hn]
    norm_num
  have hLc : Nat.card L = 3840 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center L),h.center_quotient_card hc,hzcard,hn]
    norm_num
  have hQc : Nat.card Q = 64 := by
    have hfixed : Nat.card (ChapterC.blockFixed L) = Nat.card (center L) :=
      Nat.card_congr (subgroupOfEquivOfLe (h.center_le_module hc)).toEquiv
    change Nat.card ((ChapterC.blockU L).map L.subtype) = 64
    rw [card_map_of_injective L.subtype_injective,
      card_eq_card_quotient_mul_card_subgroup (ChapterC.blockFixed L),hfixed,hzcard]
    rw [show Nat.card (ChapterC.blockU L ⧸ ChapterC.blockFixed L) = 2^(n*2) from h.module_card,hn]
    norm_num
  have hf := source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique
  obtain ⟨P,hP⟩ := hf.2.2.1
  have hP' : (P : Subgroup L).map L.subtype = R := hP
  have hRc : Nat.card R = 256 := by
    rw [←hP',card_map_of_injective L.subtype_injective,P.card_eq_multiplicity,hLc]
    decide +kernel
  have hRL : R ≤ L := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1
  have hQR : Q ≤ R := by
    rw [←hP']
    exact map_mono (hc ▸ (pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal P)
  let : IsElementaryAbelian 2 (ChapterC.blockU L) := h.2.1.elementary
  have hQelem : IsElementaryAbelian 2 Q := IsElementaryAbelian.map L.subtype
  have hLQ : L ≤ normalizer (Q : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  have hN : normalizer (Q : Set G) = normalizer (L : Set G) := by
    change normalizer (sourceModule L : Set G) = _
    rw [(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2]
    exact lemma_2_4_11_1 d hG T hST hsingle hL hM hTM hunique
  let a := MulAut.conj x⁻¹
  have hRnorm := (d.lemma_2_4_8_1 hG T hST hsingle h).2.2
  have haR : R.map a.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp (hRnorm (T.inv_mem hxT))
  have hZR : Z ≤ R := by
    rw [←hP']
    exact map_mono ((h.center_le_module hc).trans
      (hc ▸ (pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal P))
  have hZcent : Z ≤ centralizer (R : Set G) := by
    rintro z ⟨w,hw,rfl⟩ r hr
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨r,hRL hr⟩)
  have hZQa : (center K).map K.subtype ≤ Q.map a.toMonoidHom := by
    rw [hZeq]
    have he := source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS
    exact ((le_inf hZR hZcent).trans_eq he.symm).trans inf_le_right
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have he := psl_three_four_opposite_center K L Q R a q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hq hLK hQR hRL
    hQelem hQc hLc hRc haR hLQ hN hZeq hZc hZQa
  have hxn : x ∈ normalizer (Z : Set G) := by
    have hh : x⁻¹ ∈ normalizer (Z : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
    simpa only [inv_inv] using (normalizer (Z : Set G)).inv_mem hh
  have hHZ : d.H ≤ normalizer (Z : Set G) := by
    have hHL : d.H ≤ normalizer (L : Set G) := by
      let := d.L0_normal
      have hh := d.L0.le_normalizer_map d.H.subtype
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,d.H.range_subtype,hsingle] at hh
      exact hh
    exact hHL.trans (normalizer_le_normalizer_characteristic_image L (center L))
  have hZS : Z ≤ S := hZR.trans (sSup_le fun _ hA => hA.1)
  have hZn : (Z.subgroupOf d.H).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hZS.trans (map_subtype_le _))).mpr hHZ
  have hZne : Z ≠ ⊥ := by
    intro hh
    exact hZ ((map_injective L.subtype_injective) (hh.trans (Subgroup.map_bot _).symm))
  have hbarrier := lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le Z hZne hZS hZn
  exact hxS (hbarrier ▸ (show x ∈ (T : Subgroup G) ⊓ normalizer (Z : Set G) from ⟨hxT,hxn⟩))
end CFSG.Quasithin.Chapter2.LinearShadows.Single
