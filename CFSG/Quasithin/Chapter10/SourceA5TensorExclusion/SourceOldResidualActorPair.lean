module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualRecognitionComplete

/-!
# Both original tensor factors in the actual overgroup action

The original component L and old residual K have nontrivial, distinct
images on every normal overgroup module containing the tensor line.
Their A₅ sections force the two restricted action kernels to be two-groups.
Restriction to the normal overcomponent and its solvable action kernel
places both images at the same literal full Sylow subgroup.

This supplies the common local markings and kernels used in the linear
and G₂ Cartan rows. The earlier nonzero overgroup core and centralization
of the original tensor line remain explicit source inputs.

Source: Aschbacher--Smith9.3.6--9, printed pp.733--734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterA.Section03 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

private theorem local_five_kernel_two {X Y : Type*} [Group X] [Finite X] [Group Y]
    (B S : Subgroup X) (hB : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (f : X →* Y) (hne : B.map f ≠ ⊥) :
    IsPGroup 2 (f.subgroupMap B).ker := by
  have ht : (⊤ : Subgroup B).IsCComponent := by
    simpa only [subgroupOf_self] using hB.subgroupOf_of_le
      (show B ≤ B from le_rfl) (show B ≤ B ⊔ S from le_sup_left)
  let := ht.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup B) ≃* B).toMonoidHom) topEquiv.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  have hk : (f.subgroupMap B).ker ≠ ⊤ := by
    intro he
    apply hne
    apply eq_bot_iff.mpr
    rintro x ⟨b,hb,rfl⟩
    have h : (⟨b,hb⟩ : B) ∈ (f.subgroupMap B).ker := he ▸ mem_top _
    exact congrArg Subtype.val (show f.subgroupMap B ⟨b,hb⟩ = 1 from h)
  have hc : (f.subgroupMap B).ker ≤ pCore 2 B := by
    rw [← PerfectCoreTwoExtension.radical_eq_core]
    exact kernel_le_solvableRadical_of_top_isCComponent ht _ hk
  exact pCore_isPGroup.of_injective (inclusion hc) (inclusion_injective hc)

include m in
/-- The original L and K retain their two-kernels and their common full
Sylow marking on the literal action quotient. -/
theorem old_residual_pair_action_data
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (W : Subgroup M₀) [W.Normal] (hUW : m.tensorLine.subgroupOf M₀ ≤ W) :
    let J := pResidual 2 M₀
    let B := ((pResidual 2 H).map H.subtype).subgroupOf M₀
    let C := L.subgroupOf M₀
    let q := actionMk W
    J.IsCComponent ∧ C ≤ J ∧ B ≤ J ∧
      IsPGroup 2 (q.subgroupMap C).ker ∧ IsPGroup 2 (q.subgroupMap B).ker ∧
      C.map q ≠ B.map q ∧
      (B.map q).subgroupOf (J.map q) < ⊤ ∧
      Group.IsSolvable (q.subgroupMap J).ker ∧
      ∃ R : Sylow 2 J,
        (R : Subgroup J) =
          (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀).subgroupOf J ∧
        (B.map q).subgroupOf (J.map q) ∈
          localCComponents (R.mapSurjective (q.subgroupMap_surjective J)) ∧
        (C.map q).subgroupOf (J.map q) ∈
          localCComponents (R.mapSurjective (q.subgroupMap_surjective J)) := by
  dsimp only
  let K := (pResidual 2 H).map H.subtype
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let B := K.subgroupOf M₀
  let C := L.subgroupOf M₀
  let J := pResidual 2 M₀
  let q := actionMk W
  have hLM : L ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_left
  have hKM : K ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_right
  have hSM : S ≤ M₀ := hgen ▸ le_sup_right
  have hUM : m.tensorLine ≤ M₀ := by
    apply (le_inf m.tensorLine_le_sylow ?_).trans hSM
    apply m.tensorLine_le_fullModule.trans
    rw [←m.module_eq]
    exact D.module_le_orbit.trans
      (source_nonnormal_orbit_le_normalizer D m.sylow_not_normalizes_component)
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  have hmove := m.old_residual_moves_tensorPlane hH hlarge
  have hout : ¬ M₀ ≤ D.maximalLocal := fun hh =>
    source_hstar_residual_not_le (le_normalizer_componentOrbit L T) hH (hKM.trans hh)
  obtain ⟨P,hP⟩ := source_a5_local_outside_overgroup_sylow D e
    m.sylow_not_normalizes_component hcore hLM hSM hout
  have hPS : (P : Subgroup M₀) = S.subgroupOf M₀ := by
    apply map_injective M₀.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSM]
  have hSyl : Chapter1.IsSylowIn 2 S (K ⊔ S) :=
    (show Chapter1.IsSylowIn 2 S M₀ from ⟨P,hP⟩).restrict
      le_sup_right (sup_le hKM hSM)
  obtain ⟨hJ,hCJ,hBJ,_⟩ := m.old_residual_component_product
    m.sylow_not_normalizes_component hH eK hSyl M₀ hcore hgen hKU hmove
  have hClocal : C ∈ localCComponents P := by
    rw [hPS]
    exact SourceEmbeddings.local_restrict
      (localCComponents_antitone inf_le_left D.maximal.1.1) hLM
  have hBlocal : B ∈ localCComponents P := by
    rw [hPS]
    exact SourceEmbeddings.local_restrict
      (m.old_residual_mem_local_at_stabilizer m.sylow_not_normalizes_component hH eK hSyl).1 hKM
  let c : C ≃* L := subgroupOfEquivOfLe hLM
  let b : B ≃* K := subgroupOfEquivOfLe hKM
  let ec : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e
  let eb : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eK
  have hBfix : B ≤ centralizer (m.tensorLine.subgroupOf M₀ : Set M₀) := by
    intro k hk u hu
    exact Subtype.ext (hKU hk u hu)
  have hCmove : ¬ C ≤ centralizer (m.tensorLine.subgroupOf M₀ : Set M₀) := by
    intro hc
    have hh : m.tensorLine ≤ centralizer (L : Set G) := by
      intro u hu l hl
      exact (congrArg Subtype.val
        (hc (show (⟨l,hLM hl⟩ : M₀) ∈ C from hl) ⟨u,hUM hu⟩ hu)).symm
    exact m.tensorLine_ne_bot (le_bot_iff.mp
      (m.fullModule_component_fixed_eq_bot ▸ le_inf m.tensorLine_le_fullModule hh))
  have hker : q.ker ≤ centralizer (m.tensorLine.subgroupOf M₀ : Set M₀) := by
    simpa only [q,actionMk,QuotientGroup.ker_mk'] using centralizer_le hUW
  have hCne : C.map q ≠ ⊥ := fun he => hCmove
    (((map_eq_bot_iff C).mp he).trans hker)
  have hBne : B.map q ≠ ⊥ := by
    intro he
    have hbW : B ≤ centralizer (W : Set M₀) := by
      simpa only [q,actionMk,QuotientGroup.ker_mk'] using (map_eq_bot_iff B).mp he
    have hBW := iSup_conjugates_le_of_le_normalizer
      (m.tensorLine.subgroupOf M₀) C W hUW le_normalizer_of_normal
    have horbit : (componentOrbit (m.tensorLine.subgroupOf M₀) C).map M₀.subtype =
        m.tensorPlane := by
      rw [map_componentOrbit,map_subgroupOf_eq_of_le hUM,map_subgroupOf_eq_of_le hLM]
      rfl
    apply hmove
    intro k hk v hv
    obtain ⟨v',hv',rfl⟩ := horbit ▸ hv
    exact congrArg Subtype.val (hbW (show (⟨k,hKM hk⟩ : M₀) ∈ B from hk) v' (hBW hv'))
  have hne : C.map q ≠ B.map q := by
    intro he
    have hc : C ≤ B ⊔ q.ker := by
      rw [←comap_map_eq]
      exact map_le_iff_le_comap.mp he.le
    exact hCmove (hc.trans (sup_le hBfix hker))
  obtain ⟨hp,_,hk,R,hR,hBR⟩ := m.old_residual_action_image_data
    m.sylow_not_normalizes_component hH eK hSyl M₀ hcore hgen hKU hmove W hUW
  let : Group.IsSolvable (q.subgroupMap J).ker := hk
  have hCR : C.subgroupOf J ∈ localCComponents R := by
    rw [hR,←hPS]
    exact SourceEmbeddings.local_restrict hClocal hCJ
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hCR (q.subgroupMap J)
  have himage : (C.subgroupOf J).map (q.subgroupMap J) = (C.map q).subgroupOf (J.map q) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact mem_map.mpr ⟨a,ha,rfl⟩
    · rintro ⟨a,ha,hax⟩
      exact ⟨⟨a,hCJ ha⟩,ha,Subtype.ext hax⟩
  exact ⟨hJ,hCJ,hBJ,local_five_kernel_two C P hClocal ec q hCne,
    local_five_kernel_two B P hBlocal eb q hBne,hne,hp,hk,R,hR,hBR,by
      simpa only [himage,Sylow.coe_mapSurjective] using hm⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
