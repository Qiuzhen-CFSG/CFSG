module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import Theory.GroupTheory.SylowCentralizerOfNormalizer
public import CFSG.Quasithin.Chapter4.Section02.Unitary.SourceSetup

/-!
# Original point-centralizer conditions for pushing up

For a T-invariant original chosen module U, set H=C_G(t), M=N_G(K),
and Q=O2(KT). The genuine uniqueness theorem for KT controls N_G(U)
and every nontrivial characteristic subgroup of Q. Even characteristic
and the central point give the local characteristic-two conditions at H∩M.
The original chosen module lies in Z(Q).

These are the common original-source conditions used in12.2.12(2) and
12.7.5 (Aschbacher--Smith, printed pp.798,840). The vector-stabilizer
component, its section-centralizer Sylow, and the C.4.8 classification
are separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original two-core Q is a Sylow subgroup of the full centralizer
of the unchanged chosen module. -/
theorem original_chosen_module_centralizer_sylow
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T K) (D : ChosenModule T K U)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) :
    ∃ P : Sylow 2 (centralizer (U : Set G)),
      (P : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
        (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨P,hP⟩ := T.exists_centralizer_sylow_of_normalizes U hTU
  refine ⟨P,hP.trans ?_⟩
  have hOrbit : componentOrbit U (T : Subgroup G) = U :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer U (T : Subgroup G) U le_rfl hTU)
      (le_componentOrbit U _)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hc := (D.fundamentalSetup h).sylow_centralizer_module hu
  simpa only [D.fundamentalSetup_module, hOrbit, Chapter3.Section02.localJoin,
    D.localOrbit_eq] using hc

/-- The local and characteristic-normalizer conditions of C.2.8 on the
same original point, component normalizer, two-core and chosen module. -/
theorem original_chosen_point_pushingUp_local
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T K) (D : ChosenModule T K U)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) (t : U) (ht : t ≠ 1) :
    let H := centralizer ({(t : G)} : Set G)
    let M := normalizer (K : Set G)
    let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
    IsSQTK KnownSimple.IsKnownSimple H ∧ H.pCoreIn 2 ≠ ⊥ ∧
      generalizedFitting (H ⊓ M : Subgroup G) = pCore 2 (H ⊓ M : Subgroup G) ∧
      Q ≤ H ⊓ M ∧
      (Q.subgroupOf H).characteristicNormalizerClosure ≤ (H ⊓ M).subgroupOf H ∧
      U ≤ (center Q).map Q.subtype ∧
      H ⊓ normalizer (U : Set G) ≤ H ⊓ M := by
  let H := centralizer ({(t : G)} : Set G)
  let M := normalizer (K : Set G)
  let Q := (K ⊔ (T : Subgroup G)).pCoreIn 2
  let := D.elementary
  have htG : (t : G) ≠ 1 := fun he => ht (Subtype.ext he)
  have hpow : (t : G)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ t.property
  have hlocal : IsTwoLocal H := isTwoLocal_involution_centralizer
    (orderOf_eq_prime hpow htG)
  have hQH : Q ≤ H := D.core_centralizes.trans
    (centralizer_le (Set.singleton_subset_iff.mpr t.property))
  have hJM : K ⊔ (T : Subgroup G) ≤ M := sup_le K.le_normalizer D.sylow_normalizes_component
  have hQM : Q ≤ M := (pCoreIn_le 2 _).trans hJM
  have hcoreMQ : M.pCoreIn 2 ≤ Q := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M)
    · have hMT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
        have hh := pCoreIn_le_sylow M (T.subtype D.sylow_normalizes_component)
        change M.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf M).map M.subtype at hh
        rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ M from
          D.sylow_normalizes_component)] at hh
      exact hMT.trans le_sup_right
    · exact hJM.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))
  have hmax := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hMH : H ⊓ M ∈ Chapter1.He G := by
    refine Chapter1.lemma_1_1_4_4 (N := H ⊓ M) ?_ inf_le_right
      (Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
        hmax.1.1 D.sylow_normalizes_component) ?_
    · intro he
      have htQ := D.le_core t.property
      have htM : (t : G) ∈ H ⊓ M := ⟨hQH htQ,hQM htQ⟩
      exact htG (mem_bot.mp (he ▸ htM))
    · exact inf_le_left.trans (hcoreMQ.trans (le_inf hQH hQM))
  have hnorm : normalizer (U : Set G) ≤ M :=
    D.normal_subgroup_normalizer_le h (D.le_sylow.trans le_sup_right) D.ne_bot
      (sup_le D.normalizes hTU)
  have hcontrol : Q.characteristicNormalizerClosure ≤ M := by
    have hnQ : K ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
      (K ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
    apply (characteristicNormalizerClosure_le_iff _ _).mpr
    intro B hB hne
    let := hB
    exact D.normal_subgroup_normalizer_le h
      ((map_subtype_le B).trans (pCoreIn_le 2 _))
      (fun he => hne ((B.map_eq_bot_iff_of_injective Q.subtype_injective).mp he))
      (hnQ.trans (normalizer_le_normalizer_characteristic_image Q B))
  refine ⟨h.simpleQTKE.twoLocal_sqtk hlocal, Chapter1.mem_H_of_isTwoLocal hlocal,
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp hMH),
    le_inf hQH hQM, ?_, ?_, inf_le_inf_left H hnorm⟩
  · have hc := characteristicNormalizerClosure_subgroupOf_le hQH hcontrol
    intro g hg
    exact ⟨g.property,hc hg⟩
  · intro u hu
    refine ⟨⟨u,D.le_core hu⟩,mem_center_iff.mpr ?_,rfl⟩
    intro q
    exact Subtype.ext (mem_centralizer_iff.mp (D.core_centralizes q.property) u hu).symm

end CFSG.Quasithin.Chapter12.Section07
