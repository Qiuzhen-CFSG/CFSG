module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Selection
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.ReducedModule
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Ordering
public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.Action
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The original normalizer configuration of 15.1.1

Write V = V(M), R = C_T(V), and N = N_M(R). Sylow Frattini in
C_M(V) shows that N induces the whole action of M on V. In particular
V is also the conjugate span of the original central involutions under N.
Reducedness of this literal source module then gives O₂(N) = R.

Ordering maximality makes N a uniqueness subgroup. For each original
minimal overgroup H outside M, the resulting configuration satisfies
case (II) of 3.1.5 and the genuine D.1.1 hypotheses. No qrc alternatives
or quadratic-ratio estimates are assumed or asserted here.

Source: Aschbacher--Smith, 15.1.1(1) and its proof, printed pp.1083--1084;
A.5.7(2), printed p.62.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The source local normalizer N_M(C_T(V(M))). -/
abbrev sourceNormalizer (T : Sylow 2 G) (M : Subgroup G) : Subgroup G :=
  M ⊓ normalizer ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G) : Set G)

omit [Finite G] in
private theorem sylow_le_sourceNormalizer (T : Sylow 2 G) {M : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) : (T : Subgroup G) ≤ sourceNormalizer T M := by
  refine le_inf hTM ?_
  exact (le_inf (T : Subgroup G).le_normalizer
    ((hTM.trans (le_normalizer_conjugateSpanBy _ _)).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

/-- The actual Sylow Frattini factorization covers the action on V(M). -/
theorem sourceNormalizer_covers_action (T : Sylow 2 G) {M : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) : OrderingLE T M (sourceNormalizer T M) := by
  let V := localModule T M
  let C := (centralizer (V : Set G)).subgroupOf M
  have hMV : M ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (hMV.trans (normalizer_le_normalizer_centralizer _))
  obtain ⟨P, hP⟩ := (T.subtype hTM).exists_subgroupOf_eq_of_normal C
  let R := (P : Subgroup C).map C.subtype
  have hR : R.map M.subtype = (T : Subgroup G) ⊓ centralizer (V : Set G) := by
    rw [show R = (P : Subgroup C).map C.subtype from rfl, hP, map_map]
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨hc, c.property⟩
    · intro hx
      exact ⟨⟨⟨x, hTM hx.1⟩, hx.2⟩, hx.1, rfl⟩
  have hf : normalizer (R : Set M) ⊔ C = ⊤ := P.normalizer_sup_eq_top
  intro m hm
  have hm' : (⟨m, hm⟩ : M) ∈ normalizer (R : Set M) ⊔ C := hf ▸ mem_top _
  obtain ⟨n, hn, c, hc, he⟩ := mem_sup_of_normal_right.mp hm'
  have hnR : (n : G) ∈ normalizer (R.map M.subtype : Set G) :=
    R.le_normalizer_map M.subtype (mem_map_of_mem M.subtype hn)
  rw [hR] at hnR
  exact ⟨n, ⟨n.property, n.property, hnR⟩, c, ⟨c.property, hc⟩,
    congrArg Subtype.val he⟩

/-- The normalizer generates the same original module; no new module is chosen. -/
theorem sourceNormalizer_module_eq (T : Sylow 2 G) {M : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) :
    localModule T (sourceNormalizer T M) = localModule T M :=
  le_antisymm (conjugateSpanBy_mono le_rfl inf_le_left)
    (sourceModule_le_of_orderingLE (sourceNormalizer_covers_action T hTM))

private theorem module_le_sourceNormalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    localModule T M ≤ sourceNormalizer T M := by
  have hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
  have hred := localModule_reduced_from_source hG T hH
  have hVM : localModule T M ≤ M := conjugateSpanBy_le_self
    (fun z hz => hM.2 ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
  have hVT : localModule T M ≤ (T : Subgroup G) := by
    have h := (map_mono hred.le_pCore).trans (pCoreIn_le_sylow M (T.subtype hM.2))
    simpa only [map_subgroupOf_eq_of_le hVM,
      Sylow.coe_subtype, map_subgroupOf_eq_of_le hM.2] using h
  exact hVT.trans (sylow_le_sourceNormalizer T hM.2)

theorem sourceNormalizer_mem_H
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    sourceNormalizer T M ∈ Chapter1.HOver G (T : Set G) := by
  have hH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
  let := localModule_elementary_from_source hG T hH
  have hVcore : localModule T M ≤ (sourceNormalizer T M).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
      (module_le_sourceNormalizer hG T hM)
      (inf_le_left.trans (le_normalizer_conjugateSpanBy _ _))
  refine ⟨?_, sylow_le_sourceNormalizer T hM.2⟩
  intro he
  exact centralInvolutions_ne_bot_of_maximal_local T hM
    (bot_unique ((le_conjugateSpanBy _ _).trans (hVcore.trans_eq he)))

/-- Original A.5.7(2): the normalizer's two-core is exactly C_T(V(M)). -/
theorem sourceNormalizer_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    (sourceNormalizer T M).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (localModule T M : Set G) := by
  let N := sourceNormalizer T M
  let V := localModule T M
  let R := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hTN : (T : Subgroup G) ≤ N := sylow_le_sourceNormalizer T hM.2
  have hred := localModule_reduced_from_source hG T (sourceNormalizer_mem_H hG T hM)
  rw [sourceNormalizer_module_eq T hM.2] at hred
  apply le_antisymm
  · refine le_inf ?_ ?_
    · simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTN] using
        pCoreIn_le_sylow N (T.subtype hTN)
    · rintro x ⟨n, hn, rfl⟩ v hv
      have hvN := module_le_sourceNormalizer hG T hM hv
      exact congrArg N.subtype ((le_centralizer_iff.mp hred.le_centralizer_pCore)
        hn ⟨v, hvN⟩ hv)
  · exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (le_inf (inf_le_left.trans hM.2) R.le_normalizer) inf_le_right

/-- Reducedness on the actual D.1.1 action image, with the kernel identified. -/
theorem sourceNormalizer_actionImage_reduced
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    pCore 2 (ChapterD.internalActionImage (sourceNormalizer T M) (localModule T M)
      (inf_le_left.trans (le_normalizer_conjugateSpanBy _ _))) = ⊥ := by
  let N := sourceNormalizer T M
  let V := localModule T M
  have hNV : N ≤ normalizer (V : Set G) := inf_le_left.trans (le_normalizer_conjugateSpanBy _ _)
  let f := ChapterE.DihedralCubic.conjugation N V hNV
  have hred := localModule_reduced_from_source hG T (sourceNormalizer_mem_H hG T hM)
  rw [sourceNormalizer_module_eq T hM.2] at hred
  let := hred.normal
  have hk : f.ker = centralizer (V.subgroupOf N : Set N) := by
    rw [ChapterE.DihedralCubic.conjugation_ker]
    ext n
    constructor
    · intro hn v hv
      exact Subtype.ext (hn v hv)
    · intro hn v hv
      exact congrArg N.subtype (hn ⟨v, module_le_sourceNormalizer hG T hM hv⟩ hv)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  change pCore 2 f.range = ⊥
  rw [← pCore_map_iso 2 e, hred.quotient_pCore_eq_bot, Subgroup.map_bot]

/-- Full source 15.1.1(1), on every original minimal overgroup outside M. -/
theorem source_lemma_15_1_1_1
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    Chapter3.QrcHypotheses T M (sourceNormalizer T M) H (localModule T M) := by
  have hHM : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1, hM.1.2⟩
  exact ⟨sylow_le_sourceNormalizer T hM.1.2, inf_le_left, hH,
    module_le_sourceNormalizer hG T hM.1,
    inf_le_left.trans (le_normalizer_conjugateSpanBy _ _),
    localModule_elementary_from_source hG T hHM,
    sourceNormalizer_actionImage_reduced hG T hM.1,
    sourceNormalizer_twoCore hG T hM.1,
    Or.inr (inf_le_right.trans (le_normalizer_conjugateSpanBy _ _))⟩

/-- The actual qrc consumer also discharges the common-normal exclusion. -/
theorem source_15_1_1_qrcConfiguration
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ChapterD.QRCConfiguration (sourceNormalizer T M) H (T : Subgroup G)
      (localModule T M) := by
  let d := source_lemma_15_1_1_1 hG T hM hH
  apply d.toQRCConfiguration
  apply d.no_common_normal
  intro L hL hNL
  exact (lemma_A_5_7_1 hM (sylow_le_sourceNormalizer T hM.1.2) inf_le_left
    (sourceNormalizer_covers_action T hM.1.2) L hL).mp hNL

/-- The first alternative of the source qrc theorem is impossible: the
actual generated group has trivial two-core. -/
theorem sourceNormalizer_join_twoCore_eq_bot
    (T : Sylow 2 G) {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    pCore 2 (sourceNormalizer T M ⊔ H : Subgroup G) = ⊥ := by
  apply twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup _ _ M
  · intro L hL hNL
    exact (lemma_A_5_7_1 hM (sylow_le_sourceNormalizer T hM.1.2) inf_le_left
      (sourceNormalizer_covers_action T hM.1.2) L hL).mp hNL
  · exact hH.1.2

end CFSG.Quasithin.Chapter15.Section01
