module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerJanko
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpComponents
public import Theory.Representation.BinaryNaturalDual.FirstCohomology

/-!
# The full doubled orbit in the pushing-up configuration

The actual section-centralizer conjugator fixes the doubled orbit setwise.
Consequently the full orbit, distinct from its original seed, lies in the
full omega-center module in C.2.8. The inclusion-induced residual quotient
and commutator generation remain unchanged.

In degree five, reciprocal containment contradicts the component's relative
normality. The genuine SL₅(2) quotient excludes the constrained components.
The full orbit has no fixed vectors and embeds in the ordinary component's
central quotient with two-rank ten; the residual's cubic rank and factor 31
then leave precisely J₄. The full central cover is retained.

Source: Aschbacher--Smith 4.2.3--13 and 4.4.6, pp.608--612,620.
The consumer NormalizerComplete excludes this cover using nonsingular control.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
open Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  {n : ℕ} (B : DoubledBranch T L V n)

include D h in
theorem doubledOrbit_le_fullModule :
    componentOrbit V (T : Subgroup G) ≤
      Chapter4.Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let F := D.fundamentalSetup h.toHypothesis1221
  let W := componentOrbit V (T : Subgroup G)
  let := D.doubledOrbit_elementary h
  have hWQ : W ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    simpa only [F, D.fundamentalSetup_module, Chapter3.Section02.localJoin, D.localOrbit_eq]
      using F.module_le_core
  have hQW : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (W : Set G) := by
    simpa only [F, D.fundamentalSetup_module, Chapter3.Section02.localJoin, D.localOrbit_eq]
      using F.core_centralizes_module
  have hWO : W ≤ Stellmacher.omegaOneCenterAmbient ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
    intro w hw
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ w).mpr
    exact ⟨hWQ hw,elemPow_eq_one_of_isElementaryAbelian w hw,
      fun q hq => (hQW hq w hw).symm⟩
  exact (D.doubledOrbit_commutator_component h).trans_le (commutator_mono hWO le_rfl)

include D h B in
theorem doubledOrbit_fullModule_conjugate
    (c : sectionCentralizerIn (normalizer (L : Set G)) L) :
    componentOrbit V (T : Subgroup G) ≤
      Chapter4.Section02.Unitary.fullModule L
        (((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom) := by
  have hL : L.map (MulAut.conj (c : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp c.property.1
  have hW : (componentOrbit V (T : Subgroup G)).map (MulAut.conj (c : G)).toMonoidHom =
      componentOrbit V (T : Subgroup G) := by
    apply mem_normalizer_iff_map_conj_eq.mp
    rw [D.doubledOrbit_normalizer_eq h B.orbit_eq]
    exact c.property.1
  have hh := map_mono (f := (MulAut.conj (c : G)).toMonoidHom) (D.doubledOrbit_le_fullModule h)
  rwa [Chapter4.Section02.Unitary.fullModule_map,hL,hW] at hh

include D h B in
theorem doubledOrbit_pushingUp_full_configuration
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H U : Subgroup G, Witness L V A J H U ∧
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      componentOrbit V (T : Subgroup G) = ⁅componentOrbit V (T : Subgroup G),F⁆ ∧
      componentOrbit V (T : Subgroup G) ≤ F := by
  have hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨(D.doubledNormalizer_unique h).1,sup_le L.le_normalizer D.sylow_normalizes_component,
      (D.doubledNormalizer_unique h).2⟩
  have hcomm := ((le_sectionCentralizer_iff A L).mp
    (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2
  obtain ⟨J,H,U,hw,c,hs,hspan,hspan',hcore,hcore',heq,hU⟩ :=
    aligned_witness_of_not_unique h.toHypothesis1221 D hM A (hA.trans inf_le_left)
      hcomm ho ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T))) hnot
  have hWU : componentOrbit V (T : Subgroup G) ≤ U := by
    rw [hU,heq]
    exact D.doubledOrbit_fullModule_conjugate h B c
  have hWJ := (D.doubledOrbit_oddActorResidual_cover h A hA ho).2.2.1.trans hw.2.1.1
  refine ⟨J,H,U,hw,hWU,hWJ,?_,?_⟩
  · have hQW : L.pCoreIn 2 ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
      apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
        (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
      simpa only [D.fundamentalSetup_module, Chapter3.Section02.localJoin, D.localOrbit_eq] using
        (D.fundamentalSetup h.toHypothesis1221).core_centralizes_module
    exact (D.doubledOrbit_commutator_component h).trans
      (commutator_eq_of_product_centralizing_factor hw.2.2.2.2.2.2.2.1 (le_centralizer_iff.mp hQW))
  · have hc := hw.2.2.2.2.2.2.1
    have hn := hw.2.2.2.2.2.2.2.2.1
    have hspanF : conjugateSpanBy _ (H ⊓ normalizer (L : Set G)) =
        (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype :=
      le_antisymm (conjugateSpanBy_le le_rfl
        ((normal_subgroupOf_iff_le_normalizer hc.component_le).mp hn)) (le_conjugateSpanBy _ _)
    exact hWU.trans (hspanF ▸ hc.module_le)

include B in
omit [Finite G] in
theorem doubledOrbit_fixed_eq_bot :
    componentOrbit V (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  apply bot_unique
  rintro v ⟨hv,hc⟩
  let w : componentOrbit V (T : Subgroup G) := ⟨v,hv⟩
  have hw : (B.coordinates w).toAdd ∈ Representation.OneCohomology.fixed
      (BinaryNaturalDual.naturalDualRepresentation
        (V := BinaryLinear.OuterCyclic.Space n)) := by
    intro g
    obtain ⟨l,rfl⟩ := B.componentProjection_surjective g
    have he : B.componentConjugation l w = w := by
      apply Subtype.ext
      exact mul_inv_eq_of_eq_mul (hc l l.property)
    exact congrArg Multiplicative.toAdd
      ((B.coordinates_componentConjugation l w).symm.trans (congrArg B.coordinates he))
  rw [BinaryNaturalDual.naturalDual_fixed_eq_bot (by have := B.degree; omega)] at hw
  have hw1 : B.coordinates w = 1 :=
    congrArg Multiplicative.ofAdd (show (B.coordinates w).toAdd = 0 from hw)
  exact congrArg Subtype.val (B.coordinates.injective (hw1.trans (map_one B.coordinates).symm))

open Chapter12.Section05.NaturalSource
open Chapter1.RadicalExclusions
private theorem normal_of_binaryFive_core_quotient
    {B : Subgroup G} (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hB : B.IsCComponent)
    (e : (B ⧸ pCore 2 B) ≃* Representation.SL5TenDimensional.Group) : B.Normal := by
  let Q := Representation.SL5TenDimensional.Group
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup Q := Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
  let : Group.IsPerfect Q := Atlas.sl_perfect 5 (by decide)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    rcases (inferInstance : (center (B ⧸ pCore 2 B)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · let : Group.IsPerfect (B ⧸ pCore 2 B) :=
        Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  let : Group.IsPerfect (B ⧸ pCore 2 B) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsQuasisimple (B ⧸ pCore 2 B) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hr : 2 ≤ primeRank 3 (B ⧸ pCore 2 B) := by
    rw [primeRank_congr 3 (e.trans Representation.SL5TenDimensional.projectiveEquiv)]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
  exact hB.normal_of_coprime_core_center_primeRank (by decide : Odd 3)
    (by rw [hz]; simp) hr (hG.stronglyQuasithin 3 (by decide) (by decide))


private abbrev Five := Representation.SL5TenDimensional.Group
private instance five_simple : IsSimpleGroup Five := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  exact Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
private instance five_perfect : Group.IsPerfect Five := Atlas.sl_perfect 5 (by decide)

private theorem five_card : Nat.card Five = 9999360 := by
  rw [Nat.card_congr Representation.SL5TenDimensional.projectiveEquiv.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  calc
    _ = ∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ)) := by
      simpa only [Nat.card_zmod, Nat.reduceSub, Nat.gcd_one_right, mul_one] using hc
    _ = 9999360 := by decide

private theorem five_center : center Five = ⊥ := by
  rcases (inferInstance : (center Five).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative Five (center_eq_top_iff.mp ht)).elim


private theorem central_kernel_le_twoCore
    {F K : Type*} [Group F] [Finite F] [Group K]
    (e : (F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group)
    (j : F →* K) (hj : Function.Injective j) :
    ((QuotientGroup.mk' (center K)).comp j).ker ≤ pCore 2 F := by
  let π : F →* Representation.SL5TenDimensional.Group := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  intro x hx
  have hc : j x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  have hcx : x ∈ center F := mem_center_iff.mpr (fun y => hj (by
    simpa only [map_mul] using mem_center_iff.mp hc (j y)))
  have hcπ : π x ∈ center Representation.SL5TenDimensional.Group := mem_center_iff.mpr (by
    intro y
    obtain ⟨z,rfl⟩ := hs y
    simpa only [map_mul] using congrArg π (mem_center_iff.mp hcx z))
  have he : π x = 1 := by simpa only [five_center,mem_bot] using hcπ
  apply (QuotientGroup.eq_one_iff x).mp
  exact e.injective (he.trans (map_one e).symm)


include D in
private theorem doubled_pushingUp_placed_local
    {F K : Subgroup G} [Group.IsPerfect F]
    (hFK : F ≤ K) (hVF : V ≤ F) (hFL : F ≤ L)
    (hm : V = ⁅V,F⁆)
    (e : (F ⧸ pCore 2 F) ≃* Representation.SL5TenDimensional.Group) :
    ExteriorComponentLocalData (K ⧸ center K) := by
  let j := inclusion hFK
  let f := (QuotientGroup.mk' (center K)).comp j
  let W := V.subgroupOf F
  have hFW : F ≤ normalizer (V : Set G) := hFL.trans D.normalizes
  have hn : (⊤ : Subgroup F) ≤ normalizer (W : Set F) := by
    intro x _ y
    exact hFW x.property (y : G)
  let := D.elementary
  have hP : IsPGroup 2 (W.map f) := (IsElementaryAbelian.isPGroup 2 V).comap_subtype.map f
  have hne : W.map f ≠ ⊥ := by
    intro hb
    have hk := (map_eq_bot_iff W).mp hb
    have hc : V ≤ centralizer (F : Set G) := by
      intro v hv y hy
      have hz : j (⟨v,hVF hv⟩ : F) ∈ center K :=
        (QuotientGroup.eq_one_iff _).mp (hk hv)
      have he : (⟨y,hy⟩ : F) * ⟨v,hVF hv⟩ = ⟨v,hVF hv⟩ * (⟨y,hy⟩ : F) :=
        (inclusion_injective hFK) (by
          simpa only [map_mul] using mem_center_iff.mp hz (j ⟨y,hy⟩))
      exact congrArg Subtype.val he
    exact D.ne_bot (hm.trans (commutator_eq_bot_iff_le_centralizer.mpr hc))
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.to_le
    (central_kernel_le_twoCore e j (inclusion_injective hFK))
  have hr : 2 ≤ primeRank 3 F := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 F) pCore_isPGroup,
      primeRank_equiv 3 (e.trans Representation.SL5TenDimensional.projectiveEquiv)]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
  have hr' : primeRank 3 f.range = primeRank 3 F := by
    rw [MonoidHom.range_eq_map f]
    exact (ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) f hk
      (⊤ : Subgroup F)).trans (primeRank_equiv 3 Subgroup.topEquiv)
  have h31F : 31 ∣ Nat.card F := by
    have hd : 31 ∣ Nat.card (F ⧸ pCore 2 F) := by
      rw [Nat.card_congr e.toEquiv,five_card]
      decide
    exact hd.trans (card_quotient_dvd_card _)
  have h31 : 31 ∣ Nat.card f.range := by
    have hcount : Nat.card f.ker * Nat.card f.range = Nat.card F := by
      rw [←index_ker]
      exact f.ker.card_mul_index
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    have hc : Nat.Coprime 31 (Nat.card f.ker) := by
      rw [hn]
      exact (by decide : Nat.Coprime 31 2).pow_right n
    exact hc.dvd_of_dvd_mul_left (hcount.symm ▸ h31F)
  refine ⟨f.range,W.map f,Group.IsPerfect.range f,hr' ▸ hr,hP,hne,?_,map_le_range f W,h31⟩
  simpa only [←MonoidHom.range_eq_map] using
    (map_mono (f := f) hn).trans (W.le_normalizer_map f)


include D h in
theorem doubledFive_pushingUp_escape (B : DoubledBranch T L V 5)
    {A J H U : Subgroup G} (hw : Witness L V A J H U) :
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H := by
  intro hf
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hn,hmove,hVF,⟨e,he⟩,hrest⟩
  let M := normalizer (L : Set G)
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let := h.quasisimple
  let : IsQuasisimple (F ⧸ pCore 2 F) := IsQuasisimple.of_mulEquiv e.symm
  have hM : IsMaximalTwoLocal M := (D.doubledNormalizer_unique h).1
  have hne : H ≠ M := fun he => hstrict.ne (by rw [he,inf_idem])
  have hs := h.simpleQTKE.twoLocal_sqtk hM.1
  have hd := reciprocal_setup hH hM hs hne hf
  have hFL : F = L := residual_eq_of_fitting_contained L.le_normalizer le_rfl hH hM hs hne hcover hf
  obtain ⟨hcomp,hnorm,hi⟩ := index_two_of_fitting_contained hc hn hstrict hd.1 hf
  have hLH : L ≤ H := hFL ▸ (map_subtype_le (solvableResidual (L ⊓ H : Subgroup G))).trans inf_le_right
  let eL : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hLH
  let q := (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans
    (B.component.trans ((BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5)).symm.trans
      Representation.SL5TenDimensional.projectiveEquiv.symm))
  have hcompL : (L.subgroupOf H).IsCComponent := hFL ▸ hcomp
  have hnormL : normalizer (L.subgroupOf H : Set H) = M.subgroupOf H := hFL ▸ hnorm
  let : (L.subgroupOf H).Normal := normal_of_binaryFive_core_quotient hc.sqtk hcompL q
  rw [normalizer_eq_top] at hnormL
  rw [←hnormL,index_top] at hi
  norm_num at hi

include D h B in
theorem doubledOrbit_cover_quotient_injective
    {F K : Subgroup G} (hWK : componentOrbit V (T : Subgroup G) ≤ K) (hFK : F ≤ K)
    (hcover : (L : Set G) = (F : Set G) * (L.pCoreIn 2 : Set G)) :
    Function.Injective ((QuotientGroup.mk' (center K)).comp (inclusion hWK)) := by
  let f := (QuotientGroup.mk' (center K)).comp (inclusion hWK)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_bot_iff.mp
  intro x hx
  have hz : inclusion hWK x ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
  have hcore : L.pCoreIn 2 ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
    simpa only [D.fundamentalSetup_module, Chapter3.Section02.localJoin, D.localOrbit_eq] using
      (D.fundamentalSetup h.toHypothesis1221).core_centralizes_module
  have hxc : (x : G) ∈ centralizer (F : Set G) := by
    intro y hy
    exact congrArg K.subtype (mem_center_iff.mp hz (inclusion hFK ⟨y,hy⟩))
  have hxl : (x : G) ∈ centralizer (L : Set G) := by
    intro y hy
    obtain ⟨a,ha,b,hb,rfl⟩ := hcover ▸ (show y ∈ (L : Set G) from hy)
    calc
      (a * b) * (x : G) = a * (b * x) := mul_assoc _ _ _
      _ = a * (x * b) := congrArg (a * ·) ((hcore hb) x x.property).symm
      _ = x * (a * b) := by rw [←mul_assoc,hxc a ha,mul_assoc]
  apply Subtype.ext
  exact (show (x : G) ∈ (⊥ : Subgroup G) from doubledOrbit_fixed_eq_bot B ▸ ⟨x.property,hxl⟩)

include D h in
theorem doubledFive_pushingUp_ordinary_janko (B : DoubledBranch T L V 5)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWU : componentOrbit V (T : Subgroup G) ≤ U)
    (K : Subgroup H) (hK : IsComponent H K) :
    Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hN,hmove,hVF,⟨e,he⟩,hrest⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Kg := K.map H.subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hFK : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hUK : U ≤ Kg := by
    have hh := map_mono (f := H.subtype) ((hc.ordinary_module_placement K hK).1.trans inf_le_right)
    rwa [map_subgroupOf_eq_of_le (hc.module_le.trans (conjugateSpanBy_le
      (hc.component_le.trans hc.local_le) (hc.local_le.trans H.le_normalizer)))] at hh
  have hWK := hWU.trans hUK
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let : IsQuasisimple K := hK.2
  let q : Kg ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let z := centerQuotientCongr q
  have hkg := hc.sqtk.subgroup K
  have hmodel := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
    hkg.stronglyQuasithin.quasithin hkg.isKGroup
  have hr : 10 ≤ primeRank 2 (K ⧸ center K) := by
    have hi := D.doubledOrbit_cover_quotient_injective h B hWK hFK hcover
    let W := componentOrbit V (T : Subgroup G)
    let := D.doubledOrbit_elementary h
    let : IsElementaryAbelian 2 (⊤ : Subgroup W) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup W).subtype (⊤ : Subgroup W).subtype_injective
    have hcW : Nat.card W = 2 ^ 10 := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
      rw [Nat.card_congr Additive.toMul,B.finrank_eq,Nat.card_zmod] at hh
      exact hh
    have hv : 10 ≤ primeRank 2 W := IsElementaryAbelian.primeRank_ge_of_card
      (⊤ : Subgroup W) (by simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup W) ≃* W).toEquiv] using hcW)
    have hh := hv.trans (Theory.GroupTheory.primeRank_le_of_injective 2 _ hi)
    rwa [primeRank_congr 2 z] at hh
  let eFive := B.component.trans ((BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5)).symm.trans
    Representation.SL5TenDimensional.projectiveEquiv.symm)
  have hlocal := (D.doubled_pushingUp_placed_local hFK hVF hFL hmove (e.trans eFive)).of_mulEquiv z
  rcases hmodel.remaining_of_twoRank_ge_eight (by omega) with ho | hb | htwo | hs | hj
  · exact (ChapterA.Section02.no_theoremB_odd_model_of_twoRank_ge_eight (by omega) ho).elim
  · exact (hlocal.not_bender hb).elim
  · obtain ⟨n,hn⟩ := htwo
    exact (hlocal.not_rank_two n hn).elim
  · obtain ⟨E,_,_,hE,⟨f⟩⟩ := hs
    have hu : primeRank 2 (Theory.SpecificGroups.SymplecticSix.PSp E) ≤ 9 := by
      apply primeRank_le_of_prime_pow_not_dvd
      intro hd
      have hh := hd.trans (card_quotient_dvd_card
        (center (Theory.SpecificGroups.SymplecticSix.Sp E)))
      rw [Theory.SpecificGroups.SymplecticSix.card_sp_of_card_two hE] at hh
      norm_num at hh
    rw [primeRank_equiv 2 f] at hr
    change 10 ≤ primeRank 2 (Theory.SpecificGroups.SymplecticSix.PSp E) at hr
    exact (by omega : False).elim
  · exact hj

include D h in
theorem doubledFive_pushingUp_janko (B : DoubledBranch T L V 5)
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H U : Subgroup G, Witness L V A J H U ∧
      componentOrbit V (T : Subgroup G) ≤ U ∧
      componentOrbit V (T : Subgroup G) ≤ J.pCoreIn 2 ∧
      ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        U.subgroupOf H ≤ K ∧
        componentOrbit V (T : Subgroup G) ≤ K.map H.subtype ∧
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  obtain ⟨J,H,U,hw,hWU,hWJ,hWF,hWF'⟩ := D.doubledOrbit_pushingUp_full_configuration h B A hA ho hnot
  have hc := hw.2.2.2.2.2.2.1
  have hN := hw.2.2.2.2.2.2.2.2.1
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hN
  have hf := D.doubledFive_pushingUp_escape h B hw
  have hf' : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H :=
    fun hh => hf (hh.trans (comap_mono inf_le_right))
  obtain ⟨e,he⟩ := hw.2.2.2.2.2.2.2.2.2.2.2.1
  let eFive := B.component.trans ((BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5)).symm.trans
    Representation.SL5TenDimensional.projectiveEquiv.symm)
  obtain ⟨K,hK,hq,hout,hFK,hcases⟩ := hc.ordinary_or_constrained_escape hf'
  have hoK : IsComponent H K := by
    rcases hcases with hoK | hcon
    · exact hoK
    · exact (exterior_no_constrained_pushingUp hc hn (e.trans eFive) K hK hq hout hcon).elim
  have hUK := (hc.ordinary_module_placement K hoK).1.trans inf_le_right
  have hWH : componentOrbit V (T : Subgroup G) ≤ H := hWJ.trans ((pCoreIn_le 2 J).trans hw.2.2.2.1)
  have hWK : componentOrbit V (T : Subgroup G) ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype) ((comap_mono hWU).trans hUK)
    change ((componentOrbit V (T : Subgroup G)).subgroupOf H).map H.subtype ≤ _ at hh
    rwa [map_subgroupOf_eq_of_le hWH] at hh
  exact ⟨J,H,U,hw,hWU,hWJ,K,hoK,hc.ordinary_component_normal K hoK,hout,hUK,hWK,
    D.doubledFive_pushingUp_ordinary_janko h B hw hWU K hoK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
