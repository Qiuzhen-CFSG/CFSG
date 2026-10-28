module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Geometry
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Radical.Source
public import CFSG.Quasithin.ChapterB.Section02.RankLifting
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.Representation.NormalElementaryQuotient

/-!
# The common omega-closure action in the escaping configuration

For the literal D=⟨Ω₁Z(R)^{KR}⟩, reducedness in KR makes O₂(KR)
centralize D. Normalization transports the centralization of the seed by
O₂(L_R) to the whole closure. Thus the images of L_R and KR commute in
Ĥ= L_RKR / C_{L_RKR}(D). The faithful binary representation below acts
by the original ambient conjugation.

Faithfulness of L_R detects its nonzero action on D. The original Sylow
omega-center lies in D, so K also acts nontrivially. A nonzero T-invariant
[D,L_R] meets Ω₁Z(T); the canonical centralizer uniqueness then proves
[[D,L_R],K]≠1. B.2.4 gives the rank bound for each actual Thompson-family
member, retaining its image under the same centralizer quotient map.

The controlled index, common chief section, FF classification and final
contradiction remain with qt-d-1319-ff-contradiction. Earlier canonical
stars and source hypotheses are discharged by qt-d-1317-supplements and
qt-d-1317-source. No chief-section or FF conclusion is assumed here.
Source: Aschbacher--Smith 13.1.9, printed pp.870--871; B.2.4, pp.75--76.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin ChapterB
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter1.RadicalNormalizers
open Chapter12.Section02 ChapterA.Section04 Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

@[expose] def commonGroup (T L Y : Subgroup G) (j : ℕ) : Subgroup G :=
  canonicalSupplement T L ⊔ (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)

@[expose] def commonModule (T L Y : Subgroup G) (j : ℕ) :
    Subgroup (commonGroup T L Y j) :=
  (omegaClosure T L Y j).subgroupOf (commonGroup T L Y j)

theorem commonModule_normal {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (j : ℕ) :
    (commonModule T L Y j).Normal := by
  have hd := omegaClosure_geometry w hTH hAH hTL j
  exact normal_subgroupOf_of_le_normalizer (sup_le (le_sup_left.trans hd.2.2.2) hd.2.2.1)

abbrev HatGroup (T L Y : Subgroup G) (j : ℕ) [(commonModule T L Y j).Normal] :=
  commonGroup T L Y j ⧸ centralizer (commonModule T L Y j : Set (commonGroup T L Y j))

@[expose] def hatMap (T L Y : Subgroup G) (j : ℕ) [(commonModule T L Y j).Normal] :
    commonGroup T L Y j →* HatGroup T L Y j := QuotientGroup.mk' _

theorem hatMap_ker (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] :
    (hatMap T L Y j).ker =
      centralizer (commonModule T L Y j : Set (commonGroup T L Y j)) := by
  unfold hatMap
  exact QuotientGroup.ker_mk' _


@[expose] def hatImage (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] (X : Subgroup G) : Subgroup (HatGroup T L Y j) :=
  (X.subgroupOf (commonGroup T L Y j)).map (hatMap T L Y j)

omit [Finite G] in
private theorem core_centralizes_of_reduced (D B : Subgroup G) (hDB : D ≤ B)
    (hr : IsPReduced 2 (D.subgroupOf B)) : B.pCoreIn 2 ≤ centralizer (D : Set G) := by
  rintro x ⟨q,hq,rfl⟩ d hd
  have he := hr.le_centralizer_pCore
    (show (⟨d,hDB hd⟩ : B) ∈ D.subgroupOf B from hd) q hq
  exact (congrArg Subtype.val he).symm

theorem commonModule_elementary (h : Hypothesis1311 T) {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) (j : ℕ) :
    IsElementaryAbelian 2 (commonModule T L Y j) := by
  let : IsElementaryAbelian 2 (omegaClosure T L Y j) :=
    (omegaClosure_elementary_le_radical h w hH hTH hAH hTL hcore j).1
  exact IsElementaryAbelian.subgroupOf
    ((omegaClosure_geometry w hTH hAH hTL j).2.1.trans le_sup_right)

@[expose] def hatRepresentation (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)] :
    Representation (ZMod 2) (HatGroup T L Y j) (Additive (commonModule T L Y j)) :=
  Representation.NormalElementaryQuotient.representation (commonModule T L Y j)
    (hatMap T L Y j) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

theorem hatRepresentation_apply (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)]
    (g : commonGroup T L Y j) (d : Additive (commonModule T L Y j)) :
    (((hatRepresentation T L Y j (hatMap T L Y j g) d).toMul : commonGroup T L Y j) : G) =
      (g : G) * ((d.toMul : commonGroup T L Y j) : G) * (g : G)⁻¹ :=
  congrArg Subtype.val (Representation.NormalElementaryQuotient.representation_apply
    (commonModule T L Y j) (hatMap T L Y j) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) g d)

theorem hatRepresentation_injective (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)] :
    Function.Injective (hatRepresentation T L Y j) :=
  Representation.NormalElementaryQuotient.representation_injective (commonModule T L Y j)
    (hatMap T L Y j) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

theorem omegaClosure_core_centralizes (h : Hypothesis1311 T) {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) (j : ℕ) :
    (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L).pCoreIn 2 ≤
      centralizer (omegaClosure T L Y j : Set G) :=
  core_centralizes_of_reduced _ _ (omegaClosure_geometry w hTH hAH hTL j).2.1
    (omegaClosure_reduced h w hH hTH hAH hTL hcore j)

theorem common_commutator_centralizes (h : Hypothesis1311 T) {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hAC : canonicalSupplement T L ≤ C)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) (j : ℕ) :
    ⁅canonicalSupplement T L,
        thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L⁆ ≤
      centralizer (omegaClosure T L Y j : Set G) :=
  (thompson_commutator_core_bound w hTH hAH hAC hTL j).trans
    (inf_le_right.trans (omegaClosure_core_centralizes h w hH hTH hAH hTL hcore j))

theorem canonical_core_centralizes_omegaClosure {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) (j : ℕ) :
    (canonicalSupplement T L).pCoreIn 2 ≤ centralizer (omegaClosure T L Y j : Set G) := by
  let A := canonicalSupplement (T : Subgroup G) L
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let K := thompsonCommutator (T : Subgroup G) L Y j
  have hQA : A.pCoreIn 2 ≤ R :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le A.le_normalizer (sylow_normalizes_canonicalSupplement hTL))).trans_eq hcore
  have hi := thompson_commutator_invariance w hTH hAH hTL j
  have hBA : K ⊔ R ≤ normalizer (A : Set G) := sup_le (hi.1.trans w.normalizes)
    ((radicalSylowCentralizer_le T L).trans (sylow_normalizes_canonicalSupplement hTL))
  apply le_centralizer_iff.mpr
  apply conjugateSpanBy_le
  · intro z hz q hq
    exact ((mem_omegaOneCenterAmbient_iff R z).mp hz).2.2 q (hQA hq)
  · exact (hBA.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))).trans
      (normalizer_le_normalizer_centralizer _)

theorem sylow_omegaCenter_le_omegaClosure (h : Hypothesis1311 T) {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) (j : ℕ) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ omegaClosure T L Y j := by
  have hchar := h.simpleQTKE.evenCharacteristic T H hH hTH
  have hQT := pCoreIn_le_sylow H (T.subtype hTH)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hQT
  apply le_trans _ (omegaClosure_geometry w hTH hAH hTL j).1
  intro z hz
  obtain ⟨hzT,hz2,hzc⟩ := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
  have hzQ : z ∈ H.pCoreIn 2 := by
    have hc : (⟨z,hTH hzT⟩ : H) ∈ centralizer (pCore 2 H : Set H) := by
      intro q hq
      exact Subtype.ext (hzc q (hQT (mem_map_of_mem H.subtype hq)))
    exact mem_map_of_mem H.subtype (hchar hc)
  exact (mem_omegaOneCenterAmbient_iff _ z).mpr
    ⟨candidate_core_le_radical hTH hAH hcore hzQ,hz2,
      fun r hr => hzc r (radicalSylowCentralizer_le T L hr)⟩

theorem omegaClosure_moved_by_K (h : Hypothesis1311 T) {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) {j : ℕ}
    (hN : normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤ normalizer (L : Set G))
    (hZ : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ⁅omegaClosure T L Y j,thompsonCommutator T L Y j⁆ ≠ ⊥ := by
  intro he
  apply (thompson_commutator_escape w hTH hN hZ).2.2.2
  exact le_bot_iff.mp ((commutator_mono
    (sylow_omegaCenter_le_omegaClosure h w hH hTH hAH hTL hcore j) le_rfl).trans he.le)

theorem omegaClosure_moved_by_canonical (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (j : ℕ) :
    ⁅omegaClosure T L Y j,canonicalSupplement T L⁆ ≠ ⊥ := by
  let A := canonicalSupplement (T : Subgroup G) L
  let R := radicalSylowCentralizer (T : Subgroup G) L
  obtain ⟨hA,hcore,_⟩ := canonical_frattini_geometry h hmany hL hn
  have hAp : IsPPerfect 2 A := mem_L_isPPerfect hA.1
  have hRp : IsPGroup 2 R := T.isPGroup'.to_le (radicalSylowCentralizer_le T L)
  have hAR : A ≤ normalizer (R : Set G) := normalizerResidual_le_normalizer _ _
  have hRA : R ≤ normalizer (A : Set G) :=
    (radicalSylowCentralizer_le T L).trans (sylow_normalizes_canonicalSupplement hTL)
  have hQR : A.pCoreIn 2 ≤ R :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le A.le_normalizer (sylow_normalizes_canonicalSupplement hTL))).trans_eq hcore
  have hnon := (signalizerModule_ne_bot_iff_intrinsic A R hAp hRp hAR hQR
    (commutator_le_pCore_of_mutual_normalization A R hRp hAR hRA)).mpr
      (canonical_intrinsicModule_ne_bot h hmany hL hn)
  intro he
  apply hnon
  rw [signalizerModule_eq_commutator_omegaCenter,commutator_comm]
  exact le_bot_iff.mp ((commutator_mono
    (omegaClosure_geometry w hTH hAH hTL j).1 le_rfl).trans he.le)

private theorem centralizer_le_of_omega_unique (T : Subgroup G) (M U : Subgroup G)
    (hu : U ≤ omegaOneCenterAmbient T) (hne : U ≠ ⊥)
    (hm : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      centralizer (omegaOneCenterAmbient T : Set G) ≤ N → N = M) :
    centralizer (U : Set G) ≤ M := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient T) := omegaOneCenterAmbient_elementaryAbelian T
  have hloc : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hne,(IsElementaryAbelian.isPGroup 2 (omegaOneCenterAmbient T)).to_le hu,rfl⟩
  obtain ⟨N,hN,hmax⟩ := Finite.exists_le_maximal hloc
  have hc := (centralizer_le_normalizer (U : Set G)).trans hN
  exact hc.trans_eq (hm N hmax ((centralizer_le hu).trans hc))

theorem omegaClosure_double_movement (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) {L H C Y : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    (hN : normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤ normalizer (L : Set G)) :
    ⁅⁅omegaClosure T L Y j,canonicalSupplement T L⁆,thompsonCommutator T L Y j⁆ ≠ ⊥ := by
  let D := omegaClosure (T : Subgroup G) L Y j
  let A := canonicalSupplement (T : Subgroup G) L
  let U := ⁅D,A⁆
  have hd := omegaClosure_geometry w hTH hAH hTL j
  have hcore := (canonical_frattini_geometry h hmany hL hn).2.1
  have hDe := omegaClosure_elementary_le_radical h w hH hTH hAH hTL hcore j
  have hUD : U ≤ D := le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hd.2.2.2)
  have hUT : U ≤ (T : Subgroup G) := hUD.trans (hDe.2.trans (radicalSylowCentralizer_le T L))
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change U.map (MulAut.conj t).toMonoidHom = U
    have hDmap : D.map (MulAut.conj t).toMonoidHom = D :=
      mem_normalizer_iff_map_conj_eq.mp ((le_sup_right.trans hd.2.2.2) ht)
    have hAmap : A.map (MulAut.conj t).toMonoidHom = A :=
      mem_normalizer_iff_map_conj_eq.mp (sylow_normalizes_canonicalSupplement hTL ht)
    rw [map_commutator,hDmap,hAmap]
  have hUne : U ≠ ⊥ := omegaClosure_moved_by_canonical h hmany hL hn w hTH hAH hTL j
  have hUZ : U ⊓ omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ := by
    obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp
      (inf_centerIn_ne_bot T.isPGroup' hUne hUT hTU)
    let : IsElementaryAbelian 2 D := hDe.1
    have hzZ : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) :=
      (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨hUT z.property.1,elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G)
          (hUD z.property.1),z.property.2.2⟩
    intro he
    exact hz (Subtype.ext (mem_bot.mp (he ▸ (show (z : G) ∈
      U ⊓ omegaOneCenterAmbient (T : Subgroup G) from ⟨z.property.1,hzZ⟩))))
  have hc := nonquasisimple_centralizer_unique_of_stars h hmany hs hL hn
  have hzM := centralizer_le_of_omega_unique (T : Subgroup G) (normalizer (L : Set G))
    (U ⊓ omegaOneCenterAmbient (T : Subgroup G)) inf_le_right hUZ hc.2.2
  intro he
  have hKM : thompsonCommutator T L Y j ≤ normalizer (L : Set G) := by
    rw [commutator_comm] at he
    exact (commutator_eq_bot_iff_le_centralizer.mp he).trans
      ((centralizer_le inf_le_left).trans hzM)
  exact (thompson_commutator_escape w hTH hN hc.2.1).2.2.1 hKM

omit [Finite G] in
private theorem relative_fixed_map (E D A : Subgroup G) (hD : D ≤ E) (hA : A ≤ E) :
    ((D.subgroupOf E) ⊓ centralizer (A.subgroupOf E : Set E)).map E.subtype =
      D ⊓ centralizer (A : Set G) := by
  ext x
  constructor
  · rintro ⟨y,⟨hyD,hyC⟩,rfl⟩
    exact ⟨hyD, fun a ha => congrArg Subtype.val (hyC ⟨a,hA ha⟩ ha)⟩
  · rintro ⟨hxD,hxC⟩
    exact ⟨⟨x,hD hxD⟩,⟨hxD,fun a ha => Subtype.ext (hxC a ha)⟩,rfl⟩


private theorem hat_images_commute_of_centralizes (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    (hc : ⁅canonicalSupplement T L,thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L⁆ ≤
      centralizer (omegaClosure T L Y j : Set G)) :
    ⁅hatImage T L Y j (canonicalSupplement T L),
      hatImage T L Y j (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)⁆ = ⊥ := by
  let A := canonicalSupplement T L
  let B := thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L
  let E := commonGroup T L Y j
  have hAE : A ≤ E := le_sup_left
  have hBE : B ≤ E := le_sup_right
  change ⁅(A.subgroupOf E).map (hatMap T L Y j),
    (B.subgroupOf E).map (hatMap T L Y j)⁆ = ⊥
  rw [← map_commutator,Subgroup.map_eq_bot_iff,hatMap_ker]
  intro x hx d hd
  have hx' := mem_map_of_mem E.subtype hx
  rw [map_commutator,map_subgroupOf_eq_of_le hAE,map_subgroupOf_eq_of_le hBE] at hx'
  exact Subtype.ext (hc hx' d hd)

theorem hat_images_commute (h : Hypothesis1311 T) {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hAC : canonicalSupplement T L ≤ C)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) (j : ℕ) [(commonModule T L Y j).Normal] :
    ⁅hatImage T L Y j (canonicalSupplement T L),
      hatImage T L Y j (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)⁆ = ⊥ :=
  hat_images_commute_of_centralizes (T : Subgroup G) L Y j
    (common_commutator_centralizes h w hH hTH hAH hAC hTL hcore j)


theorem hat_images_generate (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] :
    hatImage T L Y j (canonicalSupplement T L) ⊔
      hatImage T L Y j (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L) = ⊤ := by
  let E := commonGroup T L Y j
  have hg : (canonicalSupplement T L).subgroupOf E ⊔
      (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L).subgroupOf E = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show canonicalSupplement T L ≤ E from le_sup_left),
      map_subgroupOf_eq_of_le (show thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L ≤ E from le_sup_right),
      ← MonoidHom.range_eq_map,range_subtype]
    rfl
  simp only [hatImage]
  rw [← Subgroup.map_sup,hg]
  exact map_top_of_surjective (hatMap T L Y j) (QuotientGroup.mk'_surjective _)

theorem hat_image_eq_bot_iff (T L Y X : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    (hD : omegaClosure T L Y j ≤ commonGroup T L Y j)
    (hX : X ≤ commonGroup T L Y j) :
    hatImage T L Y j X = ⊥ ↔
      ⁅omegaClosure T L Y j,X⁆ = ⊥ := by
  simp only [hatImage]
  rw [Subgroup.map_eq_bot_iff,commutator_comm,commutator_eq_bot_iff_le_centralizer]
  rw [show (hatMap T L Y j).ker = centralizer (commonModule T L Y j : Set _) from
    QuotientGroup.ker_mk' _]
  constructor
  · intro hc x hx d hd
    have he := hc (show (⟨x,hX hx⟩ : commonGroup T L Y j) ∈ X.subgroupOf _ from hx)
    change (⟨x,hX hx⟩ : commonGroup T L Y j) ∈ centralizer (commonModule T L Y j : Set _) at he
    exact congrArg Subtype.val (he ⟨d,hD hd⟩ hd)
  · intro hc x hx d hd
    exact Subtype.ext (hc hx d hd)

private theorem omegaClosure_rank_bound_of_elementary (T L Y A : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    (hd : IsElementaryAbelian 2 (omegaClosure T L Y j) ∧
      omegaClosure T L Y j ≤ radicalSylowCentralizer T L)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer T L) j)
    (hne : hatImage T L Y j A ≠ ⊥) :
    Nat.log 2 (Nat.card (omegaClosure T L Y j)) -
        Nat.log 2 (Nat.card (omegaClosure T L Y j ⊓ centralizer (A : Set G) : Subgroup G)) ≤
      j + Nat.log 2 (Nat.card (hatImage T L Y j A)) := by
  let E := commonGroup T L Y j
  let D := omegaClosure T L Y j
  let R := radicalSylowCentralizer T L
  have hRE : R ≤ E := le_sup_right.trans le_sup_right
  have hDE : D ≤ E := hd.2.trans hRE
  have hAE : A ≤ E := hA.1.trans hRE
  let : IsElementaryAbelian 2 D := hd.1
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (commonModule T L Y j) := IsElementaryAbelian.subgroupOf hDE
  let : IsElementaryAbelian 2 (A.subgroupOf E) := IsElementaryAbelian.subgroupOf hAE
  have ha : A.subgroupOf E ∈ thompsonFamily (R.subgroupOf E) j := by
    apply (thompsonFamily_map_iff_of_injective E.subtype E.subtype_injective _ _ _).mp
    rwa [map_subgroupOf_eq_of_le hAE,map_subgroupOf_eq_of_le hRE]
  have har := (mem_thompsonFamily_iff_rank _ _ _).mp ha
  have hb := lemma_B_2_4_1 (R.subgroupOf E) (commonModule T L Y j) (A.subgroupOf E)
    (comap_mono hd.2) ha.1 j (by change _ = twoRank _ - j; omega)
    (hatMap T L Y j) (hatMap_ker T L Y j) hne
  have hDc : Nat.card (commonModule T L Y j) = Nat.card D :=
    Nat.card_congr (subgroupOfEquivOfLe hDE).toEquiv
  have hCc : Nat.card ((commonModule T L Y j) ⊓ centralizer (A.subgroupOf E : Set E) : Subgroup E) =
      Nat.card (D ⊓ centralizer (A : Set G) : Subgroup G) := by
    change Nat.card (D.subgroupOf E ⊓ centralizer (A.subgroupOf E : Set E) : Subgroup E) = _
    rw [← card_map_of_injective E.subtype_injective,
      relative_fixed_map E D A hDE hAE]
  rw [hDc,hCc] at hb
  change Nat.log 2 (Nat.card D) -
      Nat.log 2 (Nat.card (D ⊓ centralizer (A : Set G) : Subgroup G)) ≤
    j + Nat.log 2 (Nat.card ((A.subgroupOf E).map (hatMap T L Y j)))
  omega

theorem omegaClosure_rank_bound (h : Hypothesis1311 T) {L H C Y A : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) {j : ℕ} [(commonModule T L Y j).Normal]
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer T L) j)
    (hne : hatImage T L Y j A ≠ ⊥) :
    Nat.log 2 (Nat.card (omegaClosure T L Y j)) -
        Nat.log 2 (Nat.card (omegaClosure T L Y j ⊓ centralizer (A : Set G) : Subgroup G)) ≤
      j + Nat.log 2 (Nat.card (hatImage T L Y j A)) :=
  omegaClosure_rank_bound_of_elementary (T : Subgroup G) L Y A j
    (omegaClosure_elementary_le_radical h w hH hTH hAH hTL hcore j) hA hne


omit [Finite G] in
private theorem relative_image_twoCore {Q : Type*} [Group Q]
    (E D B : Subgroup G) (hBE : B ≤ E) (hDB : D ≤ B)
    (q : E →* Q) (hq : q.ker = centralizer (D.subgroupOf E : Set E))
    (hr : IsPReduced 2 (D.subgroupOf B)) :
    pCore 2 ((B.subgroupOf E).map q) = ⊥ := by
  let f : B →* (B.subgroupOf E).map q :=
    (q.subgroupMap _).comp (subgroupOfEquivOfLe hBE).symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hBE).symm.surjective
  have hk : f.ker = centralizer (D.subgroupOf B : Set B) := by
    ext b
    change f b = 1 ↔ _
    have he : f b = 1 ↔ (⟨b,hBE b.property⟩ : E) ∈ q.ker := by
      constructor
      · intro hh
        exact congrArg Subtype.val hh
      · intro hh
        exact Subtype.ext hh
    rw [he,hq]
    constructor
    · intro hb d hd
      exact Subtype.ext (congrArg (fun x : E => (x : G)) (hb ⟨d,hBE d.property⟩ hd))
    · intro hb d hd
      exact Subtype.ext (congrArg (fun x : B => (x : G)) (hb ⟨d,hDB hd⟩ hd))
  let := hr.normal
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  rw [← pCore_map_iso 2 e,hr.quotient_pCore_eq_bot,Subgroup.map_bot]

private theorem hat_second_factor_twoCore_of_reduced (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    (hD : omegaClosure T L Y j ≤ thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)
    (hr : IsPReduced 2 ((omegaClosure T L Y j).subgroupOf
      (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L))) :
    pCore 2 (hatImage T L Y j (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)) = ⊥ :=
  relative_image_twoCore (commonGroup T L Y j) (omegaClosure T L Y j)
    (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L) le_sup_right
    hD (hatMap T L Y j) (hatMap_ker T L Y j) hr

/-- Reducedness of D in KR passes to its image under the common hat map. -/
theorem hat_second_factor_twoCore (h : Hypothesis1311 T) {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) (j : ℕ) [(commonModule T L Y j).Normal] :
    pCore 2 (hatImage T L Y j
      (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)) = ⊥ :=
  hat_second_factor_twoCore_of_reduced (T : Subgroup G) L Y j
    (omegaClosure_geometry w hTH hAH hTL j).2.1
    (omegaClosure_reduced h w hH hTH hAH hTL hcore j)

omit [Finite G] in
private theorem twoGroup_centralizer_eq_bot (K R : Subgroup G)
    (hR : IsPGroup 2 R) (hRK : R ≤ normalizer (K : Set G))
    (hcore : (K ⊔ R).pCoreIn 2 = ⊥) :
    R ⊓ centralizer (K : Set G) = ⊥ := by
  let Q := R ⊓ centralizer (K : Set G)
  have hKQ : K ≤ normalizer (Q : Set G) :=
    (le_centralizer_iff.mp (show Q ≤ centralizer (K : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hRQ : R ≤ normalizer (Q : Set G) :=
    (le_inf R.le_normalizer (hRK.trans (normalizer_le_normalizer_centralizer K))).trans
      inf_normalizer_le_normalizer_inf
  apply le_bot_iff.mp
  exact (le_pCoreIn_of_normalizes (hR.to_le (show Q ≤ R from inf_le_left))
    (show Q ≤ K ⊔ R from inf_le_left.trans le_sup_right) (sup_le hKQ hRQ)).trans_eq hcore

private theorem hat_radical_faithful_of_normalized (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    (hn : commonGroup T L Y j ≤ normalizer (thompsonCommutator T L Y j : Set G))
    (hr : IsPGroup 2 (radicalSylowCentralizer T L))
    (hc : pCore 2 (hatImage T L Y j
      (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)) = ⊥) :
    hatImage T L Y j (radicalSylowCentralizer T L) ⊓
      centralizer (hatImage T L Y j (thompsonCommutator T L Y j) : Set (HatGroup T L Y j)) = ⊥ := by
  let K := thompsonCommutator T L Y j
  let R := radicalSylowCentralizer T L
  let E := commonGroup T L Y j
  let Kh := hatImage T L Y j K
  let Rh := hatImage T L Y j R
  let : (K.subgroupOf E).Normal := normal_subgroupOf_of_le_normalizer hn
  let : Kh.Normal := Normal.map inferInstance (hatMap T L Y j)
    (QuotientGroup.mk'_surjective _)
  have hR : IsPGroup 2 Rh := hr.comap_subtype.map (hatMap T L Y j)
  have he : hatImage T L Y j (K ⊔ R) = Kh ⊔ Rh := by
    unfold hatImage
    rw [subgroupOf_sup (show K ≤ E from le_sup_left.trans le_sup_right)
      (show R ≤ E from le_sup_right.trans le_sup_right),Subgroup.map_sup]
    rfl
  change pCore 2 (hatImage T L Y j (K ⊔ R)) = ⊥ at hc
  rw [he] at hc
  apply twoGroup_centralizer_eq_bot Kh Rh hR le_normalizer_of_normal
  change (pCore 2 (Kh ⊔ Rh : Subgroup (HatGroup T L Y j))).map (Kh ⊔ Rh).subtype = ⊥
  rw [hc,Subgroup.map_bot]

private theorem commonGroup_normalizes_of_invariant (T L Y : Subgroup G) (j : ℕ)
    (hi : canonicalSupplement T L ⊔ T ≤ normalizer (thompsonCommutator T L Y j : Set G)) :
    commonGroup T L Y j ≤ normalizer (thompsonCommutator T L Y j : Set G) := by
  let K := thompsonCommutator T L Y j
  have hA : canonicalSupplement T L ≤ normalizer (K : Set G) := le_sup_left.trans hi
  have hR : radicalSylowCentralizer T L ≤ normalizer (K : Set G) :=
    (radicalSylowCentralizer_le T L).trans (le_sup_right.trans hi)
  exact sup_le hA (sup_le K.le_normalizer hR)

/-- The literal centralizing kernel of the R-image on the K-image is trivial. -/
@[expose] def HatRadicalFaithful (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] : Prop :=
  hatImage T L Y j (radicalSylowCentralizer T L) ⊓
    centralizer (hatImage T L Y j (thompsonCommutator T L Y j) : Set (HatGroup T L Y j)) = ⊥

/-- The image of R acts faithfully on the image of the actual commutator K.
The kernel is a normal two-subgroup of the reduced second factor. -/
theorem hat_radical_faithful_on_commutator (h : Hypothesis1311 T)
    {L H C Y : Subgroup G} (w : RefinedWitness T L H C Y)
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) (j : ℕ) [(commonModule T L Y j).Normal] : HatRadicalFaithful (T : Subgroup G) L Y j :=
  hat_radical_faithful_of_normalized (T : Subgroup G) L Y j
    (commonGroup_normalizes_of_invariant (T : Subgroup G) L Y j
      (thompson_commutator_invariance w hTH hAH hTL j).2.2.1)
    (T.isPGroup'.to_le (radicalSylowCentralizer_le T L))
    (hat_second_factor_twoCore h w hH hTH hAH hTL hcore j)


open Representation.BinaryOffender

/-- The displacement rank in D is the fixed codimension of the literal
centralizer-quotient representation. -/
theorem hat_fixedCodim (T L Y A : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule T L Y j)]
    (hD : omegaClosure T L Y j ≤ commonGroup T L Y j)
    (hA : A ≤ commonGroup T L Y j) :
    fixedCodim (hatRepresentation T L Y j) (hatImage T L Y j A) =
      Nat.log 2 (Nat.card (omegaClosure T L Y j)) -
        Nat.log 2 (Nat.card (omegaClosure T L Y j ⊓ centralizer (A : Set G) : Subgroup G)) := by
  let E := commonGroup T L Y j
  let V := commonModule T L Y j
  let ρ := hatRepresentation T L Y j
  have hVc : Nat.card V = Nat.card (omegaClosure T L Y j) :=
    Nat.card_congr (subgroupOfEquivOfLe hD).toEquiv
  have hFc : Nat.card (fixedSpace ρ (hatImage T L Y j A)) =
      Nat.card (omegaClosure T L Y j ⊓ centralizer (A : Set G) : Subgroup G) := by
    have he : Nat.card (fixedSpace ρ (hatImage T L Y j A)) =
        Nat.card (V ⊓ centralizer (A.subgroupOf E : Set E) : Subgroup E) :=
      Nat.card_congr (Representation.NormalElementaryQuotient.fixedSpaceEquiv
        V (hatMap T L Y j) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
        (A.subgroupOf E))
    rw [he]
    change Nat.card ((omegaClosure T L Y j).subgroupOf E ⊓
      centralizer (A.subgroupOf E : Set E) : Subgroup E) = _
    rw [← card_map_of_injective E.subtype_injective,relative_fixed_map E _ A hD hA]
  have hV := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  have hF := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace ρ (hatImage T L Y j A))
  rw [Nat.card_zmod] at hV hF
  have hVl : Nat.log 2 (Nat.card (omegaClosure T L Y j)) =
      Module.finrank (ZMod 2) (Additive V) := by
    rw [←hVc,show Nat.card V = Nat.card (Additive V) from rfl,hV,Nat.log_pow (by decide)]
  have hFl : Nat.log 2 (Nat.card (omegaClosure T L Y j ⊓ centralizer (A : Set G) : Subgroup G)) =
      Module.finrank (ZMod 2) (fixedSpace ρ (hatImage T L Y j A)) := by
    rw [←hFc,hF,Nat.log_pow (by decide)]
  rw [hVl,hFl]
  exact Nat.eq_sub_of_add_eq (fixedCodim_add_finrank ρ (hatImage T L Y j A))

/-- The B.2.4 inequality for the specified image in the actual hat action. -/
@[expose] def HatActorBound (T L Y A : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule T L Y j)] : Prop :=
  IsElementaryTwo (hatImage T L Y j A) ∧
    fixedCodim (hatRepresentation T L Y j) (hatImage T L Y j A) ≤
      j + rank (hatImage T L Y j A)

private theorem hatActorBound_of_rank_bound (T L Y A : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule T L Y j)]
    (hD : omegaClosure T L Y j ≤ commonGroup T L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer T L) j)
    (hne : hatImage T L Y j A ≠ ⊥)
    (hb : Nat.log 2 (Nat.card (omegaClosure T L Y j)) -
      Nat.log 2 (Nat.card (omegaClosure T L Y j ⊓ centralizer (A : Set G) : Subgroup G)) ≤
        j + Nat.log 2 (Nat.card (hatImage T L Y j A))) : HatActorBound T L Y A j := by
  have hAE : A ≤ commonGroup T L Y j := hA.1.trans (le_sup_right.trans le_sup_right)
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A.subgroupOf (commonGroup T L Y j)) :=
    IsElementaryAbelian.subgroupOf hAE
  refine ⟨⟨hne,IsElementaryAbelian.map (hatMap T L Y j)⟩,?_⟩
  rw [hat_fixedCodim T L Y A j hD hAE]
  exact hb

/-- B.2.4 on the actual faithful hat action: the actor has rank deficit j. -/
theorem hat_actor_rank_bound (h : Hypothesis1311 T) {L H C Y A : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) {j : ℕ} [(commonModule T L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule T L Y j)]
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer T L) j)
    (hne : hatImage T L Y j A ≠ ⊥) :
    HatActorBound (T : Subgroup G) L Y A j :=
  hatActorBound_of_rank_bound (T : Subgroup G) L Y A j
    ((omegaClosure_geometry w hTH hAH hTL j).2.1.trans le_sup_right) hA hne
    (omegaClosure_rank_bound h w hH hTH hAH hTL hcore hA hne)

/-- At index zero the same bound says that the literal actor is an offender. -/
theorem HatActorBound.isOffender (T L Y A : Subgroup G)
    [(commonModule T L Y 0).Normal]
    [IsElementaryAbelian 2 (commonModule T L Y 0)]
    (h : HatActorBound T L Y A 0) :
    IsOffender (hatRepresentation T L Y 0) (hatImage T L Y 0 A) :=
  ⟨h.1, by simpa only [zero_add] using h.2⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
