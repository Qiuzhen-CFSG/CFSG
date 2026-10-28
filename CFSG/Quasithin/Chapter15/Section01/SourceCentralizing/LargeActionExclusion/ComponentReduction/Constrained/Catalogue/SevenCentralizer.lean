module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenBlock
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.SeedCentralizer
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SourceCore

/-!
# Excluding the exceptional A₇ block in the original catalogue

For every exceptional member of the original local family, the fixed-line
centralizer is the literal M_Z intersection, with index 15. Its GL₃(2)
action has trivial two-core. Thus every two-subgroup of the normalizer Sylow
normalized by that intersection centralizes the entire intrinsic block layer.
The proof retains the original central-involution seed, without replacing it
by the full omega-center or assuming ambient componenthood.

For the selected C-component, Q₁ has precisely this normalization and Sylow
placement. Its action is therefore trivial on U(L). The block centralizer
bound puts Q₁ inside O₂(LQ₁), while the original radical condition gives
the reverse inclusion. This contradicts the proved C.2.7 Thompson condition.
Hence the reconstructed A₇ FF row is an ordinary block, with the original
quotient marking. Both original primes, the actual marker, and the later
exchanged source are retained. No C.2.7 block-catalogue conclusion is assumed.

The weight-two centralizer, three-pair partition placement and generation
clauses are still required for the A₇ ConstrainedAlternatives constructor.
The other small rows, general local-family Borel placement and catalogue
exhaustiveness remain with this owner. Original 15.1.14 retains its existing
producer and final assembly owner.

Source: Aschbacher--Smith 15.1.20(2b), printed pp.1094--1095;
C.1.23(2) and C.2.7(2), printed pp.130,146.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The exceptional fixed line identifies the original marked centralizer.
It also controls every two-subgroup normalized by that same intersection. -/
theorem localFamily_exceptional_seven_control (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hb : IsExceptionalA7Block K) :
    d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
      ((d.MZ ⊓ K).subgroupOf K).index = 15 ∧
      ∀ B : Subgroup G, IsPGroup 2 B → B ≤ d.normalizerSylow K →
        d.MZ ⊓ K ≤ normalizer (B : Set G) →
          B ≤ centralizer ((blockU K).map K.subtype : Set G) := by
  let H := K ⊔ d.normalizerSylow K
  let K0 := K.subgroupOf H
  let Z := (centralInvolutions T).subgroupOf H
  let J := (d.MZ.subgroupOf H).subgroupOf K0
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  have hb0 := RankOne.ExceptionalSevenControl.exceptional_of_equiv e.symm hb
  have hB : IsBlock K0 := ⟨inferInstance,hb0.1,(inferInstance : K0.Normal).isSubnormal⟩
  obtain ⟨⟨P,hP⟩,_,hZR⟩ := d.localFamily_normalizer_setup h hTM hu hK hq hout hb.1.fitting
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    centralizer_pCore_sup_le 2 K (d.normalizerSylow K)
      (hb.1.fitting ▸ centralizer_generalizedFitting_le K)
      (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)) inf_le_right
  have hZ : Z ≤ omegaOneCenterAmbient (P : Subgroup H) := by
    intro z hz
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨?_,?_,?_⟩
    · have hh : z.val ∈ (P : Subgroup H).map H.subtype := by
        rw [hP]
        exact hZR hz
      obtain ⟨y,hy,he⟩ := hh
      exact (Subtype.ext he : y = z) ▸ hy
    · apply Subtype.ext
      exact ((mem_omegaOneCenterAmbient_iff (T : Subgroup G) (z : G)).mp hz).2.1
    · intro x hx
      exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz x
        (d.S_le_T (show (x : G) ∈ d.S from (hP ▸ mem_map_of_mem H.subtype hx).1)))
  have hJ : J ≠ ⊤ := by
    intro he
    apply hout
    intro k hk
    exact he.ge (show (⟨⟨k,mem_sup_left hk⟩,hk⟩ : K0) ∈ ⊤ from mem_top _)
  have hCJ : (centralizer (Z : Set H)).comap K0.subtype ≤ J := by
    intro k hk
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    exact ⟨hK.1 k.property,hMc.2 (by
      intro z hz
      exact congrArg Subtype.val (hk ⟨z,mem_sup_right (hZR hz)⟩ hz))⟩
  obtain ⟨hc,hi,hcontrol⟩ := RankOne.ExceptionalSevenControl.seed_centralizer_control
    K0 hB hb0 P hchar Z hZ J hJ hCJ
  have hJe : J.map e.toMonoidHom = (d.MZ ⊓ K).subgroupOf K := by
    ext k
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨hx,x.property⟩
    · intro hk
      exact ⟨e.symm k,hk.1,e.apply_symm_apply k⟩
  refine ⟨?_,?_,?_⟩
  · ext x
    constructor
    · intro hx
      have hxc := hc ▸ (show (⟨⟨x,mem_sup_left hx.2⟩,hx.2⟩ : K0) ∈ J from hx.1)
      exact ⟨hx.2,fun z hz => congrArg Subtype.val (hxc ⟨z,mem_sup_right (hZR hz)⟩ hz)⟩
    · intro hx
      have hxc : (⟨⟨x,mem_sup_left hx.1⟩,hx.1⟩ : K0) ∈
          (centralizer (Z : Set H)).comap K0.subtype :=
        fun z hz => Subtype.ext (hx.2 z hz)
      have hxJ : (⟨⟨x,mem_sup_left hx.1⟩,hx.1⟩ : K0) ∈ J := hc.symm ▸ hxc
      exact ⟨hxJ,hx.1⟩
  · rw [←hJe]
    exact (Subgroup.index_map_of_bijective e.bijective J).trans hi
  · intro B hB hBR hn
    have hBH : B ≤ H := hBR.trans le_sup_right
    have hBP : B.subgroupOf H ≤ (P : Subgroup H) := by
      intro b hb
      have hh : (b : G) ∈ (P : Subgroup H).map H.subtype := by
        rw [hP]
        exact hBR hb
      obtain ⟨y,hy,he⟩ := hh
      exact (Subtype.ext he : y = b) ▸ hy
    have hnorm : J.map K0.subtype ≤ normalizer (B.subgroupOf H : Set H) := by
      rintro x ⟨y,hy,rfl⟩
      apply mem_normalizer_iff.mpr
      intro b
      exact mem_normalizer_iff.mp (hn ⟨hy,y.property⟩) (b : G)
    have hh := hcontrol (B.subgroupOf H) hB.comap_subtype hBP hnorm
    intro b hb u hu
    obtain ⟨v,hv,rfl⟩ := hu
    have hve : e.symm v ∈ blockU K0 := by
      have heU : (blockU K0).map e.toMonoidHom = blockU K := by
        rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ e.surjective,blockU]
      obtain ⟨w,hw,he⟩ := heU ▸ hv
      have hwv : w = e.symm v := e.injective (he.trans (e.apply_symm_apply v).symm)
      exact hwv ▸ hw
    exact congrArg Subtype.val (hh (show (⟨b,hBH hb⟩ : H) ∈ B.subgroupOf H from hb)
      (e.symm v) (mem_map_of_mem K0.subtype hve))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The actual radical contradicts the exceptional fixed-line control.
The C.2.7 input is used for its proved Thompson condition, not its catalogue. -/
theorem localFamily_not_exceptional_seven (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ K)
    (hn : d.S ≤ normalizer (K : Set G)) (hQS : d.Q1 ≤ d.S) :
    ¬ IsExceptionalA7Block K := by
  intro hb
  have hnorm : d.MZ ⊓ K ≤ normalizer (d.Q1 : Set G) :=
    inf_le_left.trans (d.MZ.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ)))
  have hQ := (d.localFamily_exceptional_seven_control h hTM hu hK
    hi.quasisimple hi.outside hb).2.2 d.Q1 (isPGroup_pCoreIn 2 d.MZ)
      (le_inf hQS (hQS.trans hn)) hnorm
  let H := K ⊔ d.Q1
  let K0 := K.subgroupOf H
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hi.normalizes)
  have hb0 := RankOne.ExceptionalSevenControl.exceptional_of_equiv e.symm hb
  have hgen : K0 ⊔ d.Q1.subgroupOf H = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ H from le_sup_left)
      (show d.Q1 ≤ H from le_sup_right),subgroupOf_self]
  have hquot : IsPGroup 2 (H ⧸ K0) := isPGroup_quotient_of_sup_eq_top K0
    (d.Q1.subgroupOf H) (isPGroup_pCoreIn 2 d.MZ).comap_subtype hgen
  have hC := centralizer_blockU_le_core_of_normal K0 hb0.1.fitting hquot
  have hQcore : d.Q1 ≤ H.pCoreIn 2 := by
    intro q hq
    apply mem_map_of_mem H.subtype (x := ⟨q,mem_sup_right hq⟩)
    apply hC
    rintro u ⟨v,hv,rfl⟩
    have heU : (blockU K0).map e.toMonoidHom = blockU K := by
      rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ e.surjective,blockU]
    have hvK : e v ∈ blockU K := heU ▸ mem_map_of_mem e.toMonoidHom hv
    exact Subtype.ext (hQ hq (e v) (mem_map_of_mem K.subtype hvK))
  have heq : H.pCoreIn 2 = d.Q1 :=
    le_antisymm (source_joinCore_le_radical (source_join_input hi)) hQcore
  exact (kernel_offender_from_source hi).2.thompson (by rw [heq])

/-- The original A₇ FF row is an ordinary block. Its quotient marking
continues to agree with the original action map at both source primes. -/
theorem PreExclusionSource.constrained_seven_block
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7)) :
    IsAlternatingBlock d.L 7 ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
        ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k) := by
  obtain ⟨hn,hi,_⟩ := s.constrained_small_alternating_input (h := h)
    hG hempty hM hJ hu hf (Or.inr rfl) e
  obtain ⟨hb,he⟩ := s.constrained_seven_blocks (h := h) hG hempty hM hJ hu hf e
  exact ⟨hb.resolve_right (d.localFamily_not_exceptional_seven h hM.1.2 hu
    ⟨d.L_component.1,s.local_component⟩ hi hn
      (d.catalogue_radical_le_sylow s.centralizer_sylow hu)),he⟩

/-- The later exchanged source has the same ordinary block and marking. -/
theorem ExchangedSource.constrained_seven_block
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7)) :
    IsAlternatingBlock d.L 7 ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
        ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k) := by
  obtain ⟨hn,hi,_⟩ := s.constrained_small_alternating_input hG hempty hM hJ hu h hf (Or.inr rfl) e
  obtain ⟨hb,he⟩ := s.constrained_seven_blocks hG hempty hM hJ hu h hf e
  exact ⟨hb.resolve_right (d.localFamily_not_exceptional_seven h hM.1.2 hu
    ⟨d.L_component.1,s.local_component⟩ hi hn
      (d.catalogue_radical_le_sylow s.centralizer_sylow hu)),he⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Ordinary A₇ block recognition at the actual original marker, retaining
its prime, row and quotient marking. Original 15.1.14 remains explicit. -/
theorem PreparedChosenModule.source_preExclusion_constrained_seven_block
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7),
          ChapterC.IsAlternatingBlock d.L 7 ∧
            ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
              ∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) =
                e (d.toNormalizerImage d.L k)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf e =>
    s.constrained_seven_block (h := h) hG hempty hM hJ hu hf e⟩

end CFSG.Quasithin.Chapter15.Section01
