module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointActionImage
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointCentralGeometry

/-!
The diagonal point residual has a two-core that centralizes the original
tensor module. Its nontrivial images have two-group kernels, and the moved
point witnesses a nonzero action whenever its commutator subgroup lies in
the acted-on module. Under Thompson movement the actual component image
lies in the exact offender actor used by the source classification.

These facts connect the original group and its literal centralizer quotient
in Aschbacher–Smith9.4.1, printed p.735.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem tensorPointResidual_core_centralizes_fullModule (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    (m.tensorPointResidual v).pCoreIn 2 ≤ centralizer (D.fullModule : Set G) := by
  let f := (m.tensorPointStabilizerEquiv v hv).toMonoidHom.comp
    (m.tensorPointResidualQuotient v)
  have hf : Function.Surjective f := (m.tensorPointStabilizerEquiv v hv).surjective.comp
    (m.tensorPointResidualQuotient_surjective v hv)
  have hp : (pCore 2 (m.tensorPointResidual v)).map f ≤ pCore 2 (alternatingGroup (Fin 5)) :=
    le_sSup ⟨(inferInstance : (pCore 2 (m.tensorPointResidual v)).Normal).map f hf,
      pCore_isPGroup.map f⟩
  rw [alternatingGroup.five_twoCore_eq_bot] at hp
  intro x hx
  obtain ⟨a,ha,rfl⟩ := hx
  have hzero : f a = 1 := hp (mem_map_of_mem f ha)
  have hq : m.tensorPointResidualQuotient v a = 1 :=
    (m.tensorPointStabilizerEquiv v hv).injective (hzero.trans (map_one _).symm)
  have hk : m.quotient ⟨a,m.tensorPointResidual_le_orbit v a.property⟩ = 1 :=
    congrArg Subtype.val hq
  exact (m.centralizer_localOrbit_iff ⟨a,m.tensorPointResidual_le_orbit v a.property⟩).mpr hk


theorem tensorPointResidual_subgroupOf_kernel_isPGroup
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (H : Subgroup G) (hLH : m.tensorPointResidual v ≤ H)
    {E : Type*} [Group E]
    (f : (m.tensorPointResidual v).subgroupOf H →* E) (hne : f.ker ≠ ⊤) :
    IsPGroup 2 f.ker := by
  let B := (m.tensorPointResidual v).subgroupOf H
  let b : B ≃* m.tensorPointResidual v := subgroupOfEquivOfLe hLH
  have hLtop : (⊤ : Subgroup (m.tensorPointResidual v)).IsCComponent := by
    simpa only [subgroupOf_self] using m.tensorPointResidual_cComponent v hv
      le_rfl (m.tensorPointResidual v).le_normalizer
  have hBtop : (⊤ : Subgroup B).IsCComponent := by
    simpa only [map_top_of_surjective b.symm.toMonoidHom b.symm.surjective] using hLtop.map_equiv b.symm
  let := hBtop.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup B) ≃* B).toMonoidHom) topEquiv.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans (m.tensorPointResidualA5Equiv v hv)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  have hk : f.ker ≤ pCore 2 B := by
    rw [←PerfectCoreTwoExtension.radical_eq_core]
    exact kernel_le_solvableRadical_of_top_isCComponent hBtop f hne
  exact pCore_isPGroup.of_injective (inclusion hk) (inclusion_injective hk)

open ChapterB.InternalThompsonAction

theorem tensorPointResidual_action_ne_bot
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (H : Subgroup G) (hLH : m.tensorPointResidual v ≤ H)
    (W : Subgroup H) [W.Normal]
    (hAW : ⁅D.fullModule,m.tensorPointResidual v⁆ ≤ W.map H.subtype) :
    ((m.tensorPointResidual v).subgroupOf H).map (actionMk W) ≠ ⊥ := by
  let A := ⁅D.fullModule,m.tensorPointResidual v⁆
  let B := (m.tensorPointResidual v).subgroupOf H
  have hAH : A ≤ H := hAW.trans (map_subtype_le W)
  have hvA : (v : G) ∈ A := m.tensorPoint_mem_moved v hv hs
  have hvm : (v : G) ∈ ⁅A,m.tensorPointResidual v⁆ := (m.tensorPoint_moved_idempotent v).symm ▸ hvA
  intro he
  have hcB : B ≤ centralizer (W : Set H) := by
    simpa only [actionMk,QuotientGroup.ker_mk'] using (map_eq_bot_iff B).mp he
  have hcentral : m.tensorPointResidual v ≤ centralizer (W.map H.subtype : Set G) := by
    intro b hb w hw
    obtain ⟨a,ha,rfl⟩ := hw
    exact congrArg H.subtype (hcB (show (⟨b,hLH hb⟩ : H) ∈ B from hb) a ha)
  have hz : ⁅A,m.tensorPointResidual v⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hAW.trans (le_centralizer_iff.mp hcentral))
  exact m.tensorPoint_ne_one v hv (mem_bot.mp (hz ▸ hvm))


include m in
theorem tensorPoint_centerOrbit_component_le_offender
    (v : D.fullModule) {I : Subgroup G}
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (hr : IsPReduced 2 ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I).subgroupOf
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I : Set G)) :
    let H := I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
    let W := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I).subgroupOf H
    letI := hr.normal; letI := hr.elementary
    IsQuasisimple ((I.subgroupOf H).map (actionMk W)) →
      (I.subgroupOf H).map (actionMk W) ≤ offenderSubgroup (action W) := by
  let X := centralizer ({(v : G)} : Set G)
  let R := (T : Subgroup G) ⊓ X
  let H := I ⊔ R
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I
  let W := U.subgroupOf H
  let := hr.normal
  let := hr.elementary
  have hHX : H ≤ X := sup_le hIX inf_le_right
  have hSyl : Chapter1.IsSylowIn 2 R H :=
    (m.tensor_centralizer_sylow v.property hs).restrict le_sup_right hHX
  obtain ⟨P,hP⟩ := hSyl
  change (P : Subgroup H).map H.subtype = R at hP
  have hPR : (P : Subgroup H) = R.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right)]
  let K := I.subgroupOf H
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hHX.trans hIN)
  have hKP : K ⊔ (P : Subgroup H) = ⊤ := by
    rw [hPR]
    exact (codisjoint_subgroupOf_sup I R).eq_top
  have hJR : elementaryAbelianMaxJ (T : Subgroup G) ≤ R :=
    le_inf (sSup_le fun _ h => h.1)
      (m.thompson_centralizes_fullModule.trans
        (centralizer_le (Set.singleton_subset_iff.mpr v.property)))
  have hJP : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
    exact elementaryAbelianMaxJ_eq_of_intermediate_finite _ _ hJR inf_le_left
  have hUH : U ≤ H := by
    apply conjugateSpanBy_le ?_ (le_sup_left.trans H.le_normalizer)
    intro z hz
    have hz' := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    exact mem_sup_right ⟨hz'.1,mem_centralizer_singleton_iff.mpr
      (hz'.2.2 v (m.fullModule_le_sylow v.property)).symm⟩
  have hmove : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) := by
    intro hc
    apply hm
    intro j hj u hu
    obtain ⟨a,ha,rfl⟩ := hJP.symm ▸ hj
    exact congrArg H.subtype (hc ha ⟨u,hUH hu⟩ hu)
  change IsQuasisimple (K.map (actionMk W)) →
    K.map (actionMk W) ≤ offenderSubgroup (action W)
  intro hq
  let := hq
  exact component_le_offenderSubgroup P K W hKP hr.quotient_pCore_eq_bot hmove

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
