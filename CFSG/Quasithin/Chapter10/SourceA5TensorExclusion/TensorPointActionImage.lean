module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointFFModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.CComponent.NormalImage

/-!
The literal diagonal local subgroup keeps its A₅ quotient and full Sylow
marking in the action on a normal elementary subgroup. When the Thompson
subgroup centralizes that module, its Frattini normalizer lies in the original
maximal local and normalizes the diagonal subgroup. C-component minimality
then identifies the two action images.
Source: Aschbacher–Smith9.4.1, printed p.735.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open ChapterB.InternalThompsonAction ChapterA.Section03
variable {H : Type*} [Group H] [Finite H]

theorem source_tensor_point_local_a5_image
    (P : Sylow 2 H) (K B W : Subgroup H) [K.Normal] [W.Normal]
    (hK : K.IsCComponent) (hB : B ∈ localCComponents P) (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hBnonzero : B.map (actionMk W) ≠ ⊥)
    (hproperImage : B.map (actionMk W) < K.map (actionMk W)) :
    let q := actionMk W
    let BI := (B.map q).subgroupOf (K.map q)
    BI < ⊤ ∧ Nonempty ((BI ⧸ pCore 2 BI) ≃* alternatingGroup (Fin 5)) ∧
      Group.IsSolvable (q.subgroupMap K).ker ∧
      ∃ R : Sylow 2 K,
        (R : Subgroup K) = (P : Subgroup H).subgroupOf K ∧
        BI ∈ localCComponents (R.mapSurjective (q.subgroupMap_surjective K)) := by
  let q := actionMk W
  let BI := (B.map q).subgroupOf (K.map q)
  let f := q.subgroupMap K
  have hBIproper : BI < ⊤ := lt_top_iff_ne_top.mpr (fun he => by
    have hh := congrArg (Subgroup.map (K.map q).subtype) he
    rw [map_subgroupOf_eq_of_le (map_mono hBK),←MonoidHom.range_eq_map,range_subtype] at hh
    exact hproperImage.ne hh)
  have hBtop : (⊤ : Subgroup B).IsCComponent := by
    simpa only [subgroupOf_self] using hB.subgroupOf_of_le
      (show B ≤ B from le_rfl) (show B ≤ B ⊔ (P : Subgroup H) from le_sup_left)
  let := hBtop.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup B) ≃* B).toMonoidHom) topEquiv.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  let b := q.subgroupMap B
  have hbker : b.ker ≠ ⊤ := by
    intro he
    apply hBnonzero
    apply (Subgroup.eq_bot_iff_forall _).mpr
    rintro _ ⟨a,ha,rfl⟩
    have hm : (⟨a,ha⟩ : B) ∈ b.ker := he ▸ mem_top _
    exact congrArg Subtype.val (show b ⟨a,ha⟩ = 1 from hm)
  have hbcore : b.ker ≤ pCore 2 B := by
    rw [← PerfectCoreTwoExtension.radical_eq_core]
    exact kernel_le_solvableRadical_of_top_isCComponent hBtop b hbker
  have hb2 : IsPGroup 2 b.ker := pCore_isPGroup.of_injective
    (inclusion hbcore) (inclusion_injective hbcore)
  let eImage : (B.map q ⧸ pCore 2 (B.map q)) ≃* alternatingGroup (Fin 5) :=
    (b.pCoreQuotientEquiv (q.subgroupMap_surjective B) hb2).symm.trans eB
  let i : BI ≃* B.map q := subgroupOfEquivOfLe (map_mono hBK)
  let eBI : (BI ⧸ pCore 2 BI) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).trans eImage
  have hfk : f.ker ≠ ⊤ := by
    intro he
    apply hBnonzero
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨a,ha,rfl⟩ := hx
    have hm : (⟨a,hBK ha⟩ : K) ∈ f.ker := he ▸ mem_top _
    exact congrArg Subtype.val (show f ⟨a,hBK ha⟩ = 1 from hm)
  let : Group.IsSolvable f.ker := hK.isSolvable_of_subnormal_lt_top
    (inferInstance : f.ker.Normal).isSubnormal hfk
  refine ⟨hBIproper,⟨eBI⟩,inferInstance,?_⟩
  obtain ⟨R,hR,hBR⟩ := SourceEmbeddings.exists_local_sylow_restriction P hB hBK
    (inferInstance : K.Normal).isSubnormal
  have hlocal := Chapter1.Section02.localCComponents_map_of_solvable_ker hBR f
  have himage : (B.subgroupOf K).map f = BI := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact mem_map.mpr ⟨a,ha,rfl⟩
    · rintro ⟨a,ha,hax⟩
      exact ⟨⟨a,hBK ha⟩,ha,Subtype.ext hax⟩
  refine ⟨R,hR,?_⟩
  simpa only [himage,Sylow.coe_mapSurjective] using hlocal

end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem tensorPointResidual_action_image_data (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (W : Subgroup (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) : Subgroup G))
    [W.Normal]
    (A : Subgroup G) (hAW : A ≤ W.map
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))).subtype)
    (z : G) (hz : z ≠ 1) (hzm : z ∈ ⁅A,m.tensorPointResidual v⁆)
    (hproper : ((m.tensorPointResidual v).subgroupOf
        (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map (actionMk W) ≠
      (I.subgroupOf (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map
        (actionMk W)) :
    let H := I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
    let K := I.subgroupOf H
    let q := actionMk W
    let BI := (((m.tensorPointResidual v).subgroupOf H).map q).subgroupOf (K.map q)
    BI < ⊤ ∧ Nonempty ((BI ⧸ pCore 2 BI) ≃* alternatingGroup (Fin 5)) ∧
      Group.IsSolvable (q.subgroupMap K).ker ∧
      ∃ R : Sylow 2 K,
        (R : Subgroup K) = (((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)).subgroupOf H).subgroupOf K ∧
        BI ∈ localCComponents (R.mapSurjective (q.subgroupMap_surjective K)) := by
  let X := centralizer ({(v : G)} : Set G)
  let S := (T : Subgroup G) ⊓ X
  let H := I ⊔ S
  let K := I.subgroupOf H
  let B := (m.tensorPointResidual v).subgroupOf H
  let q := actionMk W
  have hHX : H ≤ X := sup_le hIX inf_le_right
  have hLH : m.tensorPointResidual v ≤ H := hLI.trans le_sup_left
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hHX.trans hIN)
  have hK : K.IsCComponent := hI.subgroupOf_of_le le_sup_left hHX
  have hSyl := m.tensor_centralizer_sylow v.property hs
  obtain ⟨P,hP⟩ := hSyl.restrict (show S ≤ H from le_sup_right) hHX
  change (P : Subgroup H).map H.subtype = S at hP
  have hPS : (P : Subgroup H) = S.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show S ≤ H from le_sup_right)]
  have hB : B ∈ localCComponents P := by
    rw [hPS]
    exact SourceEmbeddings.local_restrict (m.tensorPointResidual_mem_local v hv hSyl).1 hLH
  have hBK : B ≤ K := comap_mono hLI
  let b : B ≃* m.tensorPointResidual v := subgroupOfEquivOfLe hLH
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans (m.tensorPointResidualA5Equiv v hv)
  have hmove : ¬ m.tensorPointResidual v ≤ centralizer (W.map H.subtype : Set G) := by
    intro hc
    have hzero : ⁅A,m.tensorPointResidual v⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (hAW.trans (le_centralizer_iff.mp hc))
    exact hz (mem_bot.mp (hzero ▸ hzm))
  have hnonzero : B.map q ≠ ⊥ := by
    intro he
    have hc : B ≤ centralizer (W : Set H) := by
      simpa only [q,actionMk,QuotientGroup.ker_mk'] using (map_eq_bot_iff B).mp he
    apply hmove
    intro l hl w hw
    obtain ⟨u,hu,rfl⟩ := hw
    exact congrArg H.subtype (hc (show (⟨l,hLH hl⟩ : H) ∈ B from hl) u hu)
  obtain ⟨hp,he,hker,R,hR,hlocal⟩ := source_tensor_point_local_a5_image P K B W
    hK hB hBK eB hnonzero (lt_of_le_of_ne (map_mono hBK) hproper)
  exact ⟨hp,he,hker,R,hR.trans (congrArg (fun Q : Subgroup H => Q.subgroupOf K) hPS),hlocal⟩

theorem tensorPointResidual_image_eq_of_thompson_centralizes (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (W : Subgroup (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) : Subgroup G))
    [W.Normal]
    (hm : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer
      (W.map (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))).subtype : Set G)) :
    (I.subgroupOf (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map
        (actionMk W) =
      ((m.tensorPointResidual v).subgroupOf
        (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))).map (actionMk W) := by
  let X := centralizer ({(v : G)} : Set G)
  let S := (T : Subgroup G) ⊓ X
  let H := I ⊔ S
  let K := I.subgroupOf H
  let B := (m.tensorPointResidual v).subgroupOf H
  let q := actionMk W
  have hHX : H ≤ X := sup_le hIX inf_le_right
  have hLH : m.tensorPointResidual v ≤ H := hLI.trans le_sup_left
  have hK : K.IsCComponent := hI.subgroupOf_of_le le_sup_left hHX
  have hBK : B ≤ K := comap_mono hLI
  have hSyl := m.tensor_centralizer_sylow v.property hs
  obtain ⟨P,hP⟩ := hSyl.restrict (show S ≤ H from le_sup_right) hHX
  change (P : Subgroup H).map H.subtype = S at hP
  have hPS : (P : Subgroup H) = S.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show S ≤ H from le_sup_right)]
  have hBlocal : B ∈ localCComponents P := by
    rw [hPS]
    exact SourceEmbeddings.local_restrict (m.tensorPointResidual_mem_local v hv hSyl).1 hLH
  have hB : ¬ Group.IsSolvable B := by
    intro hh
    let := hh
    exact hBlocal.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (P : Subgroup H) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show B ≤ B ⊔ (P : Subgroup H) from le_sup_left)).injective)
  have hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ S :=
    le_inf (sSup_le fun _ h => h.1)
      (m.thompson_centralizes_fullModule.trans
        (centralizer_le (Set.singleton_subset_iff.mpr v.property)))
  have hJP : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
    exact elementaryAbelianMaxJ_eq_of_intermediate_finite _ _ hJS inf_le_left
  have hc : elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) := by
    intro j hj w hw
    apply Subtype.ext
    exact hm (hJP ▸ mem_map_of_mem H.subtype hj) w (mem_map_of_mem H.subtype hw)
  have hNB : normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) ≤
      normalizer (B : Set H) := by
    rw [←subgroupOf_normalizer_eq hLH]
    intro a ha
    apply m.tensorPointResidual_normalized v
    refine ⟨source_thompson_normalizer_le_of_centralizes D
      m.thompson_centralizes_fullModule ?_,hHX a.property⟩
    rw [←hJP]
    exact le_normalizer_map H.subtype (mem_map_of_mem H.subtype ha)
  have hfull : (normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H)).map q = ⊤ := by
    have hh := congrArg (map q) (thompson_frattini P W hc)
    simpa only [Subgroup.map_sup,q,actionMk,QuotientGroup.map_mk'_self,sup_bot_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using hh
  let : (B.map q).Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←hfull]
    exact (map_mono hNB).trans (le_normalizer_map q)))
  exact cComponent_map_eq_of_normal_image K B hK hBK hB q

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
