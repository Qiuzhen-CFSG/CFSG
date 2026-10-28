module
public import CFSG.Quasithin.Chapter2.Section04.BlockResidual
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks.Factors
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ChiZero

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation.Core
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The nonsolvable selected-block normality reduction

A selected block other than A₃ is a genuine local C-component. If its
containing component in the two-core normalizer is a χ₀ block, the proved
χ₀ embedding theorem makes the two components equal. The A.3.8 orbit
bound then makes the original Sylow-conjugate span normal in that normalizer.
The remaining containing-block recognition belongs to the C.1.29 assembly.
The solvable A₃ selected-block case is deliberately separate.

Source: Aschbacher–Smith, Lemma 2.4.6, printed p.528.
-/

public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.block_isCComponent_of_not_three (d : MinimalBlockSetup M)
    (h3 : ¬ ChapterC.IsAlternatingBlock d.block 3) : d.block.IsCComponent := by
  let : IsQuasisimple (d.block ⧸ pCore 2 d.block) :=
    ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks.quotient_quasisimple_of_not_three
      d.block_type.2 h3
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    d.block_type.1.subnormal d.block_type.1.short.twoPerfect

theorem MinimalBlockSetup.ambient_block_mem_L_of_not_three (d : MinimalBlockSetup M)
    (h3 : ¬ ChapterC.IsAlternatingBlock d.block 3) :
    d.block.map d.H.subtype ∈ Chapter1.L G ((d.S : Subgroup d.H).map d.H.subtype) := by
  apply (Chapter1.mem_L_map_iff d.H.subtype d.H.subtype_injective).mpr
  change (d.block.subgroupOf (d.block ⊔ (d.S : Subgroup d.H))).IsCComponent ∧ _
  rw [d.generated]
  refine ⟨(d.block_isCComponent_of_not_three h3).subgroupOf le_top, ?_, ?_⟩
  · exact Chapter1.isSylowIn_iff.mpr ⟨d.S.isPGroup',le_top,
      fun _ hp hle _ => d.S.is_maximal' hp hle⟩
  · intro hb
    have hm := congrArg (Subgroup.map d.H.subtype) hb
    rw [map_pCoreIn_of_injective 2 _ d.H.subtype d.H.subtype_injective,
      ← MonoidHom.range_eq_map, range_subtype, Subgroup.map_bot] at hm
    have hne := (d.mem_gammaEvenZero.1.elim (fun h => h.1.1) (fun h => h.1)).1
    exact hne hm


/-- Once the genuine containing component in the core normalizer is a χ0
block, the earlier embedding and orbit theorems prove the original 2.4.6
normality assertion. No orbit or normalization conclusion is assumed. -/
theorem MinimalBlockSetup.coreNormalizer_normalizes_L0_of_chiZero_overgroup
    (d : MinimalBlockSetup M)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (h3 : ¬ ChapterC.IsAlternatingBlock d.block 3)
    (K : Subgroup (normalizer (twoCore d.H : Set G)))
    (hK : K.IsCComponent)
    (hBK : (d.block.map d.H.subtype).subgroupOf (normalizer (twoCore d.H : Set G)) ≤ K)
    (hmodel : ChapterC.IsChiZeroBlock K) :
    normalizer (twoCore d.H : Set G) ≤ normalizer (d.L0.map d.H.subtype : Set G) := by
  let N := normalizer (twoCore d.H : Set G)
  let B := (d.block.map d.H.subtype).subgroupOf N
  have hMe : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  obtain ⟨hNg,_hcore,P,hP⟩ := lemma_2_4_3_1 hG.evenCharacteristic hMe
    d.mem_gammaEvenZero d.full_pair d.S le_rfl
  have hBN : d.block.map d.H.subtype ≤ N :=
    (map_subtype_le _).trans (le_normalizer_twoCore d.H)
  have hBmap : B.map N.subtype = d.block.map d.H.subtype := map_subgroupOf_eq_of_le hBN
  have hBL : B ∈ Chapter1.L N (P : Subgroup N) := by
    apply (Chapter1.mem_L_map_iff N.subtype N.subtype_injective).mp
    rw [hBmap,hP]
    exact d.ambient_block_mem_L_of_not_three h3
  have hEq := ChapterA.Section03.SourceEmbeddings.eq_of_chiZero_containing_component
    P hBL.1 hK hBK hmodel
  have hBc : B.IsCComponent := hEq.symm ▸ hK
  have hNh : N ∈ Chapter1.H G := (hNg.1.elim (fun h => h.1.1) (fun h => h.1)).1
  have hQsq := Chapter1.Section02.uniqueness_local_quotient_sqtk hG hNh
  let : Group.IsNilpotent (pCore 2 N) := pCore_isNilpotent
  have hOr := ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
    (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
    hQsq (pCore_quotient_pCore_eq_bot 2) (hBc.map_quotient (pCore 2 N))
  have hOr' := cComponent_normal_or_index_two_of_quotient hBc (pCore 2 N) hOr
  let X := conjugateSpanBy B (P : Subgroup N)
  let : X.Normal := conjugateSpanBy_sylow_normal B P hOr'
  have hX : X.map N.subtype = d.L0.map d.H.subtype := by
    rw [show X = conjugateSpanBy B (P : Subgroup N) from rfl,
      map_conjugateSpanBy, hBmap, hP, ← map_conjugateSpanBy,
      conjugateSpanBy_eq_iSup_conj]
    rfl
  rw [← hX]
  intro x hx
  exact X.le_normalizer_map N.subtype ⟨⟨x,hx⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
end CFSG.Quasithin.Chapter2
