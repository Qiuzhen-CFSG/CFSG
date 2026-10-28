module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalClassification
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# The original local FF quotient and its marked Sylow overgroup

For every constrained escaping K in L(G₁,S), retain the actual image of K
in H/C_H(U), where H=K N_S(K) and U is the original central-involution
span. The normal two-core acts trivially on U, so the original map factors
through K/O₂(K). Both its domain and image are quasisimple; consequently
its kernel is central. A.3.6 bounds this kernel by one or three. Passing
to centers gives the actual K/O₂,Z(K) isomorphism, with the original map
on every element. If the image center has order three, the core map is
already an isomorphism and its original kernel is exactly O₂(K).

The seed Z lies in U. Thus C_H(U) lies in M_Z, and the image of M_Z∩K
is a proper subgroup containing the image of the original Sylow subgroup
S∩K. Its full preimage is exactly M_Z∩K. These comparisons supply the
literal quotient and proper-overgroup inputs to the source parabolic
recognition; no ambient C-componenthood of K or S-normalization is used.

Catalogue exhaustiveness, general local-family Borel invariance, field
exclusions and block/parabolic reconstruction remain with
qt-e-1515-constrained-source-catalogue. Original 15.1.14 remains with
qt-e-1514-global-thompson-residual for discharge by
qt-e-15122-pre-exclusion-catalogue. The later quotient assembly belongs
to qt-e-1515-constrained-linear-quotient.

Source: Aschbacher--Smith 15.1.20(2), printed pp.1094--1095; A.3.6,
printed pp.43--45; the perfect central-cover comparison is intrinsic.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The literal image K* in the source FF quotient H/C_H(U). -/
@[expose] def normalizerImage (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    Subgroup ((K ⊔ d.normalizerSylow K : Subgroup G) ⧸
      centralizer (d.normalizerModule K : Set (K ⊔ d.normalizerSylow K : Subgroup G))) :=
  (K.subgroupOf (K ⊔ d.normalizerSylow K)).map (QuotientGroup.mk' _)

/-- The original inclusion and quotient, restricted to their exact image. -/
@[expose] def toNormalizerImage (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    K →* d.normalizerImage K :=
  ((QuotientGroup.mk' (centralizer (d.normalizerModule K : Set
    (K ⊔ d.normalizerSylow K : Subgroup G)))).comp (inclusion le_sup_left)).codRestrict _
      (fun x => mem_map_of_mem _ (show (inclusion le_sup_left x) ∈
        K.subgroupOf (K ⊔ d.normalizerSylow K) from x.property))

theorem toNormalizerImage_surjective (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    Function.Surjective (d.toNormalizerImage K) := by
  rintro ⟨_,⟨x,hx,rfl⟩⟩
  exact ⟨⟨x,hx⟩,rfl⟩

theorem NormalizerAction.core_le_ker {d : CaseIComponentData T M Mc V}
    {K : Subgroup G} (a : d.NormalizerAction K) :
    pCore 2 K ≤ (d.toNormalizerImage K).ker := by
  let H := K ⊔ d.normalizerSylow K
  have hh : K.pCoreIn 2 ≤ H.pCoreIn 2 := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le K.le_normalizer inf_le_right)
  intro x hx
  obtain ⟨y,hy,he⟩ := hh (mem_map_of_mem K.subtype hx)
  have he' : y = inclusion (show K ≤ H from le_sup_left) x := Subtype.ext he
  have hc := a.reduced.le_centralizer_pCore
  apply Subtype.ext
  apply (QuotientGroup.eq_one_iff _).mpr
  exact le_centralizer_iff.mp hc (he' ▸ hy)

/-- The original FF map factors through the intrinsic two-core quotient. -/
@[expose] def NormalizerAction.coreToImage {d : CaseIComponentData T M Mc V}
    {K : Subgroup G} (a : d.NormalizerAction K) :
    (K ⧸ pCore 2 K) →* d.normalizerImage K :=
  QuotientGroup.lift _ (d.toNormalizerImage K) a.core_le_ker

theorem NormalizerAction.coreToImage_mk {d : CaseIComponentData T M Mc V}
    {K : Subgroup G} (a : d.NormalizerAction K) (x : K) :
    a.coreToImage (QuotientGroup.mk' (pCore 2 K) x) = d.toNormalizerImage K x := rfl

theorem NormalizerAction.coreToImage_surjective {d : CaseIComponentData T M Mc V}
    {K : Subgroup G} (a : d.NormalizerAction K) :
    Function.Surjective a.coreToImage :=
  QuotientGroup.lift_surjective_of_surjective _ _ (d.toNormalizerImage_surjective K) _

theorem NormalizerAction.coreToImage_ker_central {d : CaseIComponentData T M Mc V}
    {K : Subgroup G} (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    a.coreToImage.ker ≤ center (K ⧸ pCore 2 K) := by
  let := hq
  let : IsQuasisimple (d.normalizerImage K) := a.quasisimple
  exact (show Covering (K ⧸ pCore 2 K) (d.normalizerImage K) from
    { toMonoidHom := a.coreToImage, surjective := a.coreToImage_surjective }).ker_le_center

/-- The actual induced map is a perfect central cover. -/
@[expose] def NormalizerAction.coreCover {d : CaseIComponentData T M Mc V}
    {K : Subgroup G} (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    PerfectCentralCovering.Cover (K ⧸ pCore 2 K) (d.normalizerImage K) where
  toMonoidHom := a.coreToImage
  surjective := a.coreToImage_surjective
  isPerfect := hq.toIsPerfect
  ker_le_center := a.coreToImage_ker_central hq

private theorem NormalizerAction.centralQuotientMap_ker
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    ((QuotientGroup.mk' (center (d.normalizerImage K))).comp (d.toNormalizerImage K)).ker =
      centralPreimage (pCore 2 K) := by
  ext x
  change QuotientGroup.mk' (center (d.normalizerImage K)) (d.toNormalizerImage K x) = 1 ↔ _
  exact (QuotientGroup.eq_one_iff (d.toNormalizerImage K x)).trans
    (SetLike.ext_iff.mp (a.coreCover hq).comap_center (QuotientGroup.mk' (pCore 2 K) x))

/-- The source quotient by O₂,Z(K), with its original action marking. -/
noncomputable def NormalizerAction.coreCenterQuotientEquiv
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    (K ⧸ centralPreimage (pCore 2 K)) ≃*
      (d.normalizerImage K ⧸ center (d.normalizerImage K)) :=
  (QuotientGroup.quotientMulEquivOfEq (a.centralQuotientMap_ker hq).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' (center (d.normalizerImage K))).comp (d.toNormalizerImage K))
      ((QuotientGroup.mk'_surjective _).comp (d.toNormalizerImage_surjective K)))

theorem NormalizerAction.coreCenterQuotientEquiv_mk
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K)) (x : K) :
    a.coreCenterQuotientEquiv hq (QuotientGroup.mk' (centralPreimage (pCore 2 K)) x) =
      QuotientGroup.mk' (center (d.normalizerImage K)) (d.toNormalizerImage K x) := by rfl

/-- A.3.6 applies to each local member, without ambient componenthood. -/
theorem localFamily_coreQuotient_center_card (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ≤ d.G1) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    Nat.card (center (K ⧸ pCore 2 K)) = 1 ∨ Nat.card (center (K ⧸ pCore 2 K)) = 3 := by
  let := h.elementary
  let := hq
  let Q := K ⧸ pCore 2 K
  have hsq := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hKsq := (IsSQTK.equiv (subgroupOfEquivOfLe hK)).mp (hsq.subgroup (K.subgroupOf d.G1))
  have hQsq : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hKsq.isKGroup.quotient (pCore 2 K)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 K) pCore_isPGroup).trans
      (hKsq.stronglyQuasithin p hp ho)
  have htop : (⊤ : Subgroup Q).IsCComponent :=
    (show IsComponent Q ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  have hc := (ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    Q hQsq (pCore_quotient_pCore_eq_bot 2) ⊤ htop).2
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hh := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_card_of_common hc
  simpa only [Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup Q) ≃* Q)).toEquiv] using hh

theorem NormalizerAction.coreToImage_ker_card {d : CaseIComponentData T M Mc V}
    {K : Subgroup G} (a : d.NormalizerAction K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hK : K ≤ d.G1) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    Nat.card a.coreToImage.ker = 1 ∨ Nat.card a.coreToImage.ker = 3 := by
  have hd := card_dvd_of_le (a.coreToImage_ker_central hq)
  rcases d.localFamily_coreQuotient_center_card hG h hK hq with hc | hc
  · exact Or.inl (Nat.dvd_one.mp (hc ▸ hd))
  · exact (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (hc ▸ hd)

/-- No central kernel remains when the FF image has cubic center. -/
theorem NormalizerAction.coreToImage_bijective_of_cubic_center
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} (a : d.NormalizerAction K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hK : K ≤ d.G1) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : Nat.card (center (d.normalizerImage K)) = 3) :
    Function.Bijective a.coreToImage := by
  have hbound : Nat.card (center (K ⧸ pCore 2 K)) ≤ 3 := by
    rcases d.localFamily_coreQuotient_center_card hG h hK hq with he | he <;> omega
  have he := Nat.card_congr (a.coreCover hq).quotientCenterEquiv.toEquiv
  apply a.coreToImage_surjective.bijective_of_nat_card_le
  calc
    Nat.card (K ⧸ pCore 2 K) =
        Nat.card ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) *
          Nat.card (center (K ⧸ pCore 2 K)) := card_eq_card_quotient_mul_card_subgroup _
    _ ≤ Nat.card (d.normalizerImage K ⧸ center (d.normalizerImage K)) * 3 := by
      rw [he]
      exact Nat.mul_le_mul_left _ hbound
    _ = Nat.card (d.normalizerImage K) := by
      rw [←hc,←card_eq_card_quotient_mul_card_subgroup]

/-- In particular, the triple-cover row identifies the actual two-core quotient. -/
noncomputable def NormalizerAction.coreQuotientEquivOfCubicCenter
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} (a : d.NormalizerAction K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hK : K ≤ d.G1) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : Nat.card (center (d.normalizerImage K)) = 3) :
    (K ⧸ pCore 2 K) ≃* d.normalizerImage K :=
  MulEquiv.ofBijective a.coreToImage
    (a.coreToImage_bijective_of_cubic_center hG h hK hq hc)

theorem NormalizerAction.coreQuotientEquivOfCubicCenter_mk
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} (a : d.NormalizerAction K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hK : K ≤ d.G1) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : Nat.card (center (d.normalizerImage K)) = 3) (x : K) :
    a.coreQuotientEquivOfCubicCenter hG h hK hq hc (QuotientGroup.mk' (pCore 2 K) x) =
      d.toNormalizerImage K x := by rfl

theorem NormalizerAction.toNormalizerImage_ker_le_coreCenter
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    (d.toNormalizerImage K).ker ≤ centralPreimage (pCore 2 K) := by
  intro x hx
  apply a.coreToImage_ker_central hq
  exact hx

theorem NormalizerAction.toNormalizerImage_ker_eq_core_of_cubic_center
    {d : CaseIComponentData T M Mc V} {K : Subgroup G} (a : d.NormalizerAction K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hK : K ≤ d.G1) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : Nat.card (center (d.normalizerImage K)) = 3) :
    (d.toNormalizerImage K).ker = pCore 2 K := by
  apply le_antisymm _ a.core_le_ker
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply (a.coreToImage_bijective_of_cubic_center hG h hK hq hc).1
  rw [map_one]
  exact hx

theorem normalizerModule_centralizer_le_marked (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hZ : centralInvolutions T ≤ d.normalizerSylow K) :
    (centralizer (d.normalizerModule K : Set (K ⊔ d.normalizerSylow K : Subgroup G))).map
      (K ⊔ d.normalizerSylow K : Subgroup G).subtype ≤ d.MZ := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨(sup_le hK (inf_le_left.trans d.S_le_G1)) x.property,hMc.2 ?_⟩
  intro z hz
  exact congrArg Subtype.val (hx ⟨z,mem_sup_right (hZ hz)⟩ (le_normalClosure hz))

theorem toNormalizerImage_ker_le_marked (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hZ : centralInvolutions T ≤ d.normalizerSylow K) :
    (d.toNormalizerImage K).ker ≤ d.MZ.subgroupOf K := by
  intro x hx
  have he := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hc := (QuotientGroup.eq_one_iff _).mp he
  exact d.normalizerModule_centralizer_le_marked hu hK hZ
    (mem_map_of_mem (K ⊔ d.normalizerSylow K : Subgroup G).subtype hc)

/-- The image of the original M_Z intersection in the original FF image. -/
@[expose] def normalizerMarkedImage (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    Subgroup (d.normalizerImage K) := (d.MZ.subgroupOf K).map (d.toNormalizerImage K)

theorem normalizerMarkedImage_comap (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hZ : centralInvolutions T ≤ d.normalizerSylow K) :
    (d.normalizerMarkedImage K).comap (d.toNormalizerImage K) = d.MZ.subgroupOf K :=
  comap_map_eq_self (d.toNormalizerImage_ker_le_marked hu hK hZ)

theorem normalizerMarkedImage_ne_top (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hZ : centralInvolutions T ≤ d.normalizerSylow K) (hout : ¬ K ≤ d.MZ) :
    d.normalizerMarkedImage K ≠ ⊤ := by
  intro he
  have hh := d.normalizerMarkedImage_comap hu hK hZ
  rw [he,comap_top] at hh
  exact hout (subgroupOf_eq_top.mp hh.symm)

theorem localFamily_normalizerMarkedImage_sylow (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S) :
    ∃ P : Sylow 2 (d.normalizerImage K),
      (P : Subgroup (d.normalizerImage K)) =
        ((d.S ⊓ K).subgroupOf K).map (d.toNormalizerImage K) ∧
      (P : Subgroup (d.normalizerImage K)) ≤ d.normalizerMarkedImage K := by
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  have hPe : (P : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  refine ⟨P.mapSurjective (d.toNormalizerImage_surjective K),?_,?_⟩
  · change (P : Subgroup K).map (d.toNormalizerImage K) = _
    rw [hPe]
  · change (P : Subgroup K).map (d.toNormalizerImage K) ≤ _
    apply map_mono
    rw [hPe]
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨d.S_le_G1 hx.1,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx.1)).symm)⟩

/-- The original local-family consumer: central quotient comparison and a proper
marked overgroup of the literal Sylow image, with all local premises discharged. -/
theorem localFamily_ff_quotient_comparison (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    ∃ a : d.NormalizerAction K,
      StarModels.Model (d.normalizerImage K) ∧
      a.coreToImage.ker ≤ center (K ⧸ pCore 2 K) ∧
      (Nat.card a.coreToImage.ker = 1 ∨ Nat.card a.coreToImage.ker = 3) ∧
      Nonempty ((K ⧸ centralPreimage (pCore 2 K)) ≃*
        (d.normalizerImage K ⧸ center (d.normalizerImage K))) ∧
      (d.normalizerMarkedImage K).comap (d.toNormalizerImage K) = d.MZ.subgroupOf K ∧
      d.normalizerMarkedImage K ≠ ⊤ ∧
      ∃ P : Sylow 2 (d.normalizerImage K),
        (P : Subgroup (d.normalizerImage K)) =
          ((d.S ⊓ K).subgroupOf K).map (d.toNormalizerImage K) ∧
        (P : Subgroup (d.normalizerImage K)) ≤ d.normalizerMarkedImage K := by
  obtain ⟨a,hm⟩ := d.localFamily_catalogue hG hempty hM hJ hu h hK hq hout hf
  have hZ := (d.localFamily_normalizer_setup h hM.1.2 hu hK hq hout hf).2.2
  exact ⟨a,hm,a.coreToImage_ker_central hq,a.coreToImage_ker_card hG h hK.1 hq,
    ⟨a.coreCenterQuotientEquiv hq⟩,d.normalizerMarkedImage_comap hu hK.1 hZ,
    d.normalizerMarkedImage_ne_top hu hK.1 hZ hout,
    d.localFamily_normalizerMarkedImage_sylow hu hK⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
