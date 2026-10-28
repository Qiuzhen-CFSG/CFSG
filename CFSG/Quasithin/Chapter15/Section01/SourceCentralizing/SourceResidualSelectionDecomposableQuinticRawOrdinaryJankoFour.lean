module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinaryJankoFourLocal
-- Intentional same-package reuse of the native, record-free J4 rank calculation.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.JankoFour

/-! The original ordinary component cannot have J4 core quotient. Its
native odd rank forces normality. The Sylow-compatible Mathieu seed in the
actual central two-cover lies in the marked local by its genuine residual
M24 member. Original seed fixed points then generate the component with
that seed, contradicting its escape. No whole-M generation is assumed. -/

public section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem m24_twoResidual : pResidual 2 Sporadic.Mathieu.M24 = ⊤ := by
  apply (pResidual_eq_top_iff 2 _).mpr
  intro N hN hq
  let := hN
  let : Group.IsNilpotent (Sporadic.Mathieu.M24 ⧸ N) := hq.isNilpotent
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)

private theorem raw_mathieu_seed_le_marked
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) (centralizer (Z1 : Set G))) (hSM : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ (centralizer (Z1 : Set G) ⊓ Mc))
    (B : Subgroup G) (hBG : B ≤ (centralizer (Z1 : Set G))) (hn : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (B : Set G))
    (hc : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (P : Sylow 2 B) (hPS : (P : Subgroup B).map B.subtype ≤ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (f : B →* Sporadic.Mathieu.M24) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : B ≤ (centralizer (Z1 : Set G) ⊓ Mc) := by
  let R := pResidual 2 B
  let K := R.map B.subtype
  let e : R ≃* K := R.equivMapOfInjective B.subtype B.subtype_injective
  let fr := f.comp R.subtype
  have hfr : Function.Surjective fr := by
    apply MonoidHom.range_eq_top.mp
    change (f.comp R.subtype).range = ⊤
    rw [MonoidHom.range_comp,range_subtype]
    rw [map_pResidual_of_surjective 2 f hf,m24_twoResidual]
  have hkr : IsPGroup 2 fr.ker := by
    rw [←MonoidHom.comap_ker]
    exact hk.comap_subtype
  let fK := fr.comp e.symm.toMonoidHom
  have hfK : Function.Surjective fK := hfr.comp e.symm.surjective
  have hkK : IsPGroup 2 fK.ker := by
    rw [←MonoidHom.comap_ker]
    exact hkr.comap_of_injective _ e.symm.injective
  have hker := Sporadic.Mathieu.ker_eq_twoCore_of_surjective_m24 fK hfK hkK
  let eqK : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24 :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fK hfK)
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eqK.symm
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hcR := normal_core_selfCentralizing hc R
  have hcK : centralizer (pCore 2 K : Set K) ≤ pCore 2 K := by
    have he : (pCore 2 R).map e.toMonoidHom = pCore 2 K := pCore_map_iso 2 e
    intro x hx
    have hxR : e.symm x ∈ pCore 2 R := hcR (by
      intro y hy
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using hx (e y) (he ▸ mem_map_of_mem _ hy))
    rw [←he]
    exact ⟨e.symm x,hxR,e.apply_symm_apply x⟩
  have hKG : K ≤ (centralizer (Z1 : Set G)) := (map_subtype_le _).trans hBG
  let H := B ⊔ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
  have hBH : B ≤ H := le_sup_left
  let : (B.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  let eb := subgroupOfEquivOfLe hBH
  have hRcomp : R.IsCComponent := isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : R.Normal).isSubnormal (isPPerfect_pResidual 2)
  have hKcomp := (hRcomp.map_equiv eb.symm).map_subtype
    (inferInstance : (B.subgroupOf H).Normal).isSubnormal
  have heK : (R.map eb.symm.toMonoidHom).map (B.subgroupOf H).subtype = K.subgroupOf H := by
    rw [map_map]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨y,hy,Subtype.ext he⟩
  rw [heK] at hKcomp
  have hO : B.pCoreIn 2 ≠ ⊥ := by
    intro he
    have ho : pCore 2 B = ⊥ := (map_eq_bot_iff_of_injective _ B.subtype_injective).mp he
    have hevery (x : B) : x = 1 := by
      have hx : x ∈ pCore 2 B := hc (by
        intro y hy
        have hy1 : y = 1 := by
          change y ∈ pCore 2 B at hy
          rwa [ho,mem_bot] at hy
        simp only [hy1,one_mul,mul_one])
      simpa only [ho,mem_bot] using hx
    let := Sporadic.Mathieu.m24_isSimpleGroup
    obtain ⟨y,hy⟩ := exists_ne (1 : Sporadic.Mathieu.M24)
    obtain ⟨x,rfl⟩ := hf y
    exact hy (by rw [hevery x,map_one])
  have hOH : B.pCoreIn 2 ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 B) ((pCoreIn_le 2 B).trans hBH)
    ((sup_le B.le_normalizer hn).trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hloc : K ∈ Chapter1.LIn (centralizer (Z1 : Set G)) ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) := ⟨hKG,Chapter1.mem_L_of_cComponent
    (fun he => hO (bot_unique (he ▸ hOH)))
    (hs.restrict le_sup_right (sup_le hBG (Chapter1.isSylowIn_iff.mp hs).2.1))
    ((map_subtype_le _).trans hBH) hKcomp⟩
  have hKM := h.raw_local_mathieuTwentyFour_le_marked hG T hempty hM hJ hu hZ hZne hloc
    inferInstance (generalizedFitting_eq_pCore_of_selfCentralizing 2 hcK) eqK
  have hgen := congrArg (Subgroup.map B.subtype) (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hgen
  exact hgen.ge.trans (sup_le hKM (hPS.trans hSM))

private theorem raw_marked_fixer
    (T : Sylow 2 G) {M Mc Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hnZ : centralInvolutions T ≤ normalizer (L : Set G))
    (hfaith : centralInvolutions T ⊓ centralizer (L : Set G) = ⊥)
    (hSyl : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (h115 : ∃ R : Sylow 2 (centralizer (Z1 : Set G)),
      (R : Subgroup (centralizer (Z1 : Set G))).map (centralizer (Z1 : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer (Z1 : Set G) ∧
      ∀ z ∈ centralInvolutions T, z ≠ 1 →
        Chapter1.Lemma115Hypotheses (centralizer (Z1 : Set G)) R Mc z) :
    ∃ P : Sylow 2 L,
      (P : Subgroup L).map L.subtype = ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L ∧
      ∃ α : MulAut L, α^2=1 ∧ α≠1 ∧ (∀ x ∈ P, α x=x) ∧
        α.fixedSubgroup.map L.subtype ≤ Mc := by
  obtain ⟨z,hz,hzne⟩ := (Subgroup.bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  let α := L.normalizerMonoidHom ⟨z,hnZ hz⟩
  have ha (x : L) : (α x : G) = z*x*z⁻¹ := rfl
  obtain ⟨R,hR,h115⟩ := h115
  have hzc : z ∈ centralizer (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) : Set G) := by
    intro x hx
    exact (h115 z hz hzne).central x (hR.symm ▸ hx)
  have hz2 : z*z=1 := by
    simpa only [(h115 z hz hzne).involution,pow_two] using pow_orderOf_eq_one z
  have hα2 : α^2=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (α (α x) : G) = x
    rw [ha,ha]
    calc
      z*(z*(x:G)*z⁻¹)*z⁻¹ = (z*z)*x*(z*z)⁻¹ := by group
      _ = x := by rw [hz2]; simp
  have hαne : α ≠ 1 := by
    intro he
    have hc : z ∈ centralizer (L : Set G) := by
      intro x hx
      have hh := ha (⟨x,hx⟩:L)
      rw [he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    have hzbot : z ∈ (⊥ : Subgroup G) := hfaith ▸ ⟨hz,hc⟩
    exact hzne (mem_bot.mp hzbot)
  obtain ⟨P,hP⟩ := hSyl
  refine ⟨P,hP,α,hα2,hαne,?_,?_⟩
  · intro x hx
    apply Subtype.ext
    rw [ha]
    exact mul_inv_eq_iff_eq_mul.mpr
      (hzc x (show (x : G) ∈ (T : Subgroup G) ⊓ centralizer (Z1 : Set G) from
        (hP ▸ mem_map_of_mem L.subtype hx).1)).symm
  · rintro _ ⟨x,hx,rfl⟩
    apply (h115 z hz hzne).centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have he := ha x
    rw [(MulAut.mem_fixedSubgroup _ _).mp hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm

private theorem raw_seed_normalized {S L : Subgroup G}
    (hn : S ≤ normalizer (L : Set G))
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = (S ⊓ L))
    (B : Subgroup L)
    (hi : ∀ a : MulAut L, (P : Subgroup L).map a.toMonoidHom = P →
      B.map a.toMonoidHom = B) : S ≤ normalizer (B.map L.subtype : Set G) := by
  have hP' : (P : Subgroup L)=(S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show S ⊓ L ≤ L from inf_le_right)]
  intro t ht
  let a := L.normalizerMonoidHom ⟨t,hn ht⟩
  have ha : (P : Subgroup L).map a.toMonoidHom = P := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [hP'] at hx ⊢
      change t * (x : G) * t⁻¹ ∈ S ⊓ L
      exact ⟨S.mul_mem (S.mul_mem ht hx.1) (S.inv_mem ht),(a x).property⟩
    · exact (Nat.card_congr (a.subgroupMap (P : Subgroup L)).toEquiv).le
  have hb := hi a ha
  have hm : (B.map L.subtype).map (MulAut.conj t).toMonoidHom = B.map L.subtype := by
    rw [map_map]
    have he : (MulAut.conj t).toMonoidHom.comp L.subtype = L.subtype.comp a.toMonoidHom := by
      ext x
      rfl
    rw [he,←map_map,hb]
  exact (mem_normalizer_iff_map_conj_eq).mpr hm

/-- J4 is excluded on the same raw ordinary component, including its
retained central two-cover and original marked involution. -/
theorem PreparedChosenModule.raw_ordinary_not_jankoFour
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    {L : Subgroup G} (hLG : L ≤ (centralizer (Z1 : Set G)))
    (hLc : IsComponent (centralizer (Z1 : Set G)) (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hnZ : centralInvolutions T ≤ normalizer (L : Set G))
    (hfaith : centralInvolutions T ⊓ centralizer (L : Set G) = ⊥)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (h115 : ∃ P : Sylow 2 (centralizer (Z1 : Set G)), (P : Subgroup (centralizer (Z1 : Set G))).map (centralizer (Z1 : Set G)).subtype = ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ∧
      ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses (centralizer (Z1 : Set G)) P Mc z)
    (hout : ¬L ≤ (centralizer (Z1 : Set G) ⊓ Mc)) : IsEmpty ((L ⧸ pCore 2 L) ≃* Janko4.Model) := by
  refine ⟨fun e => ?_⟩
  let G1 := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ G1
  let : IsQuasisimple (L.subgroupOf G1) := hLc.2
  let eL : L.subgroupOf G1 ≃* L := subgroupOfEquivOfLe hLG
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL
  have hZtwo : IsPGroup 2 (center L) := by
    rw [hcenter]
    exact pCore_isPGroup
  have hnL0 : (L.subgroupOf G1).Normal := by
    let := h.elementary
    have hsq : IsSQTK KnownSimple.IsKnownSimple G1 := caseI_centralizer_sqtk hG Z1 hZne
      ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
    have hZ' : IsPGroup 2 (center (L.subgroupOf G1)) := hZtwo.of_equiv (centerCongr eL.symm)
    obtain ⟨n,hn⟩ := hZ'.exists_card_eq
    have hc : Nat.Coprime 3 (Nat.card (center (L.subgroupOf G1))) := by
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow_right n
    have hR : 2 ≤ primeRank 3 (L.subgroupOf G1) := by
      rw [primeRank_equiv 3 eL,
        ←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 L) pCore_isPGroup,
        primeRank_equiv 3 e]
      exact CaseIComponentData.j4_odd_rank
    exact hLc.normal_of_coprime_center_primeRank 3 hc (by
      change primeRank 3 G1 < 2 * primeRank 3 (L.subgroupOf G1)
      have hh := hsq.stronglyQuasithin 3 (by decide) (by decide)
      omega)
  let ez : (L ⧸ center L) ≃* Janko4.Model :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans e
  obtain ⟨P,hP,a,ha,hne,hfix,hfixed⟩ := raw_marked_fixer T hM hnZ hfaith hSylL h115
  obtain ⟨B,hPB,hi,hgen,hself,f,hf,hk⟩ :=
    Janko4.LocalStructure.exists_sylow_mathieu_seed_of_central_two_cover ez hZtwo P a ha hne hfix
  let C := B.map L.subtype
  let eB : B ≃* C := B.equivMapOfInjective L.subtype L.subtype_injective
  have hnL : S ≤ normalizer (L : Set G) := inf_le_right.trans
    ((normal_subgroupOf_iff_le_normalizer hLG).mp hnL0)
  have hnC := raw_seed_normalized hnL P hP B hi
  have hselfC : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    eB.symm.toMonoidHom.centralizer_pCore_le_of_surjective_pKernel eB.symm.surjective
      (by rw [eB.symm.toMonoidHom.ker_eq_bot eB.symm.injective]; exact IsPGroup.of_card (n := 0) (by simp)) hself
  let Q := (P.subtype hPB).mapSurjective (f := eB.toMonoidHom) eB.surjective
  have hQ : (Q : Subgroup C).map C.subtype = S ⊓ L := by
    change (((P.subtype hPB) : Subgroup B).map eB.toMonoidHom).map C.subtype = _
    rw [map_map]
    have he : C.subtype.comp eB.toMonoidHom = L.subtype.comp B.subtype := by ext x; rfl
    rw [he,←map_map,Sylow.coe_subtype,map_subgroupOf_eq_of_le hPB,hP]
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hCM : C ≤ G1 ⊓ Mc := raw_mathieu_seed_le_marked hG T hempty hM hJ hu h hZ hZne hSylG
    (le_inf inf_le_right (inf_le_left.trans hTMc)) C
    ((map_subtype_le _).trans hLG) hnC hselfC Q
    (hQ.le.trans inf_le_left) (f.comp eB.symm.toMonoidHom) (hf.comp eB.symm.surjective)
    (by rw [←MonoidHom.comap_ker]; exact hk.comap_of_injective _ eB.symm.injective)
  have hg := congrArg (Subgroup.map L.subtype) hgen
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hg
  exact hout (le_inf hLG (hg.ge.trans (sup_le hfixed (hCM.trans inf_le_right))))

end CFSG.Quasithin.Chapter15.Section01
