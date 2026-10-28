module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSevenBlock
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.SeedCentralizer
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SourceCore

/-!
# The actual radical excludes the exceptional seven-letter block

The original central-involution seed identifies the exceptional fixed-line
centralizer with the literal marked intersection. Its intrinsic action
forces Q1 to centralize the whole block module. Characteristic two and the
actual C.2.7 source core then give Q1=O2(LQ1), contradicting its original
Thompson condition. No Case-I generation or residual prior is supplied.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem raw_exceptional_seven_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬K ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬K ≤ M)
    (hb : IsExceptionalA7Block K) :
    let N := centralizer (Z1 : Set G) ⊓ Mc
    let R := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ normalizer (K : Set G)
    N ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
      ((N ⊓ K).subgroupOf K).index = 15 ∧
      ∀ B : Subgroup G, IsPGroup 2 B → B ≤ R →
        N ⊓ K ≤ normalizer (B : Set G) →
          B ≤ centralizer ((blockU K).map K.subtype : Set G) := by
  let N := centralizer (Z1 : Set G) ⊓ Mc
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (K : Set G)
  let H := K ⊔ R
  let K0 := K.subgroupOf H
  let Z := (centralInvolutions T).subgroupOf H
  let J := (N.subgroupOf H).subgroupOf K0
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  have hb0 := RankOne.ExceptionalSevenControl.exceptional_of_equiv e.symm hb
  have hB : IsBlock K0 := ⟨inferInstance,hb0.1,(inferInstance : K0.Normal).isSubnormal⟩
  obtain ⟨_,_,⟨P,hP⟩,_,hZR⟩ := h.raw_component_thompson hG T hM hJ hu hZ hK hq hb.1.fitting hout houtM
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    centralizer_pCore_sup_le 2 K (R)
      (hb.1.fitting ▸ centralizer_generalizedFitting_le K)
      (T.isPGroup'.to_le (inf_le_left.trans (show S ≤ (T : Subgroup G) from inf_le_left))) inf_le_right
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
        ((show S ≤ (T : Subgroup G) from inf_le_left) (show (x : G) ∈ S from (hP ▸ mem_map_of_mem H.subtype hx).1)))
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
  have hJe : J.map e.toMonoidHom = (N ⊓ K).subgroupOf K := by
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

/-- The original radical and marked Sylow exclude the exceptional whole A7 block. -/
theorem PreparedChosenModule.raw_not_exceptional_seven
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (houtM : ¬K ≤ M)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) K) : ¬IsExceptionalA7Block K := by
  intro hb
  let N := centralizer (Z1 : Set G) ⊓ Mc
  let Q := N.pCoreIn 2
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSM : S ≤ N := le_inf inf_le_right (inf_le_left.trans hTMc)
  have hQS : Q ≤ S := by
    obtain ⟨P,hP⟩ := hs.restrict hSM inf_le_left
    have hh := map_mono (f := N.subtype) (pCore_isPGroup.le_sylow_of_normal P)
    rwa [hP] at hh
  have hn : S ≤ normalizer (K : Set G) := by
    apply h.raw_local_normalizes_of_oddRank hG T hZ hZne hK hi.quasisimple Nat.prime_three (by decide)
    obtain ⟨e⟩ := hb.2.1
    rw [primeRank_equiv 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 7 3 Nat.prime_three (by decide)]
  have hnorm : N ⊓ K ≤ normalizer (Q : Set G) :=
    inf_le_left.trans (N.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))
  have hQ := (raw_exceptional_seven_control hG T hM hJ hu h hZ hK
    hi.quasisimple hi.outside houtM hb).2.2 Q (isPGroup_pCoreIn 2 N)
      (le_inf hQS (hQS.trans hn)) hnorm
  let H := K ⊔ Q
  let K0 := K.subgroupOf H
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hi.normalizes)
  have hb0 := RankOne.ExceptionalSevenControl.exceptional_of_equiv e.symm hb
  have hgen : K0 ⊔ Q.subgroupOf H = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ H from le_sup_left)
      (show Q ≤ H from le_sup_right),subgroupOf_self]
  have hquot : IsPGroup 2 (H ⧸ K0) := isPGroup_quotient_of_sup_eq_top K0
    (Q.subgroupOf H) (isPGroup_pCoreIn 2 N).comap_subtype hgen
  have hC := centralizer_blockU_le_core_of_normal K0 hb0.1.fitting hquot
  have hQcore : Q ≤ H.pCoreIn 2 := by
    intro q hq
    apply mem_map_of_mem H.subtype (x := ⟨q,mem_sup_right hq⟩)
    apply hC
    rintro u ⟨v,hv,rfl⟩
    have heU : (blockU K0).map e.toMonoidHom = blockU K := by
      rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ e.surjective,blockU]
    have hvK : e v ∈ blockU K := heU ▸ mem_map_of_mem e.toMonoidHom hv
    exact Subtype.ext (hQ hq (e v) (mem_map_of_mem K.subtype hvK))
  have heq : H.pCoreIn 2 = Q :=
    le_antisymm (source_joinCore_le_radical (source_join_input hi)) hQcore
  exact (kernel_offender_from_source hi).2.thompson (by rw [heq])

end CFSG.Quasithin.Chapter15.Section01
