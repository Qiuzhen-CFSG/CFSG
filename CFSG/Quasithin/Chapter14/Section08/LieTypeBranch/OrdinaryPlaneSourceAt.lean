module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryPlaneSource
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceAssemblyAt
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceAssembly
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlockResidual
public import CFSG.Quasithin.Chapter3.Section01.Source318Complete

/-!
# The ordinary plane and complete selected source family with local inputs

The local recognition theorem makes the actual point normalizer escape,
before full-span abelianness. Under contrary plane centralization the
original reductions construct a moving faithful component. Its supplied
block geometry yields the literal diagonal contradiction, proving plane
noncentrality. This then feeds the local plus-kernel, nonabelian-exclusion,
Baumann and critical-geometry chain on the same original natural setup.

The existential result constructs one natural chosen module and flag and
uses the contrary-plane OrdinaryBlockSource for exactly that setup. Its
inputs are still genuine earlier source obligations: qt-d-13314-ordinary-blocks
owns the blocks; qt-d-1332-source owns Source1332OneTwo, local A₅ modules and
natural choice; qt-d-1222-source owns the local structural/module inputs for
guarded recognition. Final discharge stays in qt-d-1378-source and
qt-d-1381-source; these conditional exports do not finish the book theorems.
Source: Aschbacher–Smith 13.3.14 and 13.7.8–13.8.8, pp.891–893,940–949.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section03.Noncentrality
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The original diagonal contradiction uses the source escaping point
normalizer and does not assume the full span nonabelian. -/
theorem original_six_plane_noncentral_of_diagonal_source_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (diagonal : ⁅G₁.pCoreIn 2,V₂⁆ = ⊥ → OrdinaryDiagonalSource d) :
    ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥ := by
  intro hc
  have h1221 := hypothesis1221_of_maximal_natural_six d hmax eL
  have hHz := original_six_point_normalizer_mem_Hz_at d hmax eL escape
  have hTH : (T : Subgroup G) ≤ G₁ := d.first_normalizer ▸ d.line_stable
  have hP : V₁ ≠ ⊥ := by intro he; have hh := d.line_card; simp [he] at hh
  have hlocal : IsTwoLocal G₁ := by
    rw [d.first_normalizer]
    exact ⟨V₁,hP,IsPGroup.of_card (n := 1) (by simpa using d.line_card),rfl⟩
  have hHe := Chapter1.twoLocal_mem_He_of_sylow_le T
    (d.counterexample.qtke.evenCharacteristic T) hlocal hTH
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h1221.simpleQTKE T h1221.maximal_faithful.1
  have horb : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L _ L le_rfl d.normalizes_L)
      (le_componentOrbit L _)
  have hM : IsMaximalTwoLocal M := by
    simpa only [horb,←d.local_normalizer] using hu.normalizer_maximal
  have hTM : (T : Subgroup G) ≤ M := d.local_normalizer ▸ d.normalizes_L
  have hb := ordinary_reduction_b d eL h1221 hHz.2.2
  have ha := (ordinary_reduction_a d hc).2
  obtain ⟨K,hK,hKs,hm,hn,hgen,hq⟩ :=
    source_moved_component_of_guarded_sources d.counterexample.qtke T h1332
      (Chapter3.source_guardedTheorem318One d.counterexample.qtke)
      G₁ (sourceOne L T V₁) (conjugateSpanBy V₃ G₁) M hHe hlocal hTH
      (ordinary_point_residual_le_point d) (T_normalizes_one L T V₁ d.line_stable)
      ordinary_point_residual_twoPerfect (ordinary_point_residual_quotient_card d eL)
      hM hTM hHz.2.2 ha hb.2 (ordinary_reduction_c_of_plane_centralized d eL hc)
  have hmove : ⁅conjugateSpanBy V₃ G₁,K.map G₁.subtype⁆ ≠ ⊥ := by
    let B := K.map G₁.subtype
    have hB : Group.IsPerfect B := by
      let := hK.perfect
      exact Group.IsPerfect.map G₁.subtype
    have hpB : IsPPerfect 2 B := by
      let := hB
      intro N hn hp
      let := hn
      let := hp.isNilpotent
      exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
    intro hz
    have hle := twoPerfect_le_centralizingResidual hpB
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
    let := hb.1
    have hs : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hle) (inclusion_injective hle)
    let := hs
    exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (K.equivMapOfInjective G₁.subtype G₁.subtype_injective).toMonoidHom)
      (K.equivMapOfInjective G₁.subtype G₁.subtype_injective).injective)
  have hf : K.map G₁.subtype ∈ MainForward.faithfulLocalComponents T := by
    have hω : (Stellmacher.omegaOneCenterAmbient (pCore 2 G₁)).map G₁.subtype =
        Stellmacher.omegaOneCenterAmbient (G₁.pCoreIn 2) :=
      (Stellmacher.omegaOneCenterAmbient_map_injective G₁.subtype G₁.subtype_injective _).symm
    have hspanH : conjugateSpanBy V₃ G₁ ≤ G₁ :=
      conjugateSpanBy_le (d.seed_le.trans (d.chosen.le_sylow.trans hTH)) G₁.le_normalizer
    have hUi : (conjugateSpanBy V₃ G₁).subgroupOf G₁ ≤
        Stellmacher.omegaOneCenterAmbient (pCore 2 G₁) := by
      intro u hu
      have hh := ha hu
      rw [←hω] at hh
      obtain ⟨v,hv,he⟩ := hh
      exact (G₁.subtype_injective he) ▸ hv
    have hmi : ⁅(conjugateSpanBy V₃ G₁).subgroupOf G₁,K⁆ ≠ ⊥ := by
      intro he
      have hh := congrArg (fun A : Subgroup G₁ => A.map G₁.subtype) he
      rw [map_commutator,map_subgroupOf_eq_of_le hspanH,Subgroup.map_bot] at hh
      exact hmove hh
    exact (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mpr
      (source_component_faithful_local T G₁ hTH (Chapter1.mem_H_of_isTwoLocal hlocal)
        hHe K _ hK hUi hmi)
  have b := diagonal hc K hK hKs hm hn hgen hq hmove hf
  have hnG : sourceOne L T V₁ ≤ normalizer (K.map G₁.subtype : Set G) := by
    have hh := (map_mono hn).trans (K.le_normalizer_map G₁.subtype)
    rwa [map_subgroupOf_eq_of_le (ordinary_point_residual_le_point d)] at hh
  have hpK := Chapter1.Section02.Adequate.mem_L_isPPerfect
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mp hf).1
  let J := Diagonal.localGroup (K.map G₁.subtype) (sourceOne L T V₁) T
  have hJH : J ≤ G₁ := sup_le
    (sup_le (map_subtype_le _) (ordinary_point_residual_le_point d)) hTH
  have hPT : V₁ ≤ (T : Subgroup G) :=
    d.line_le_plane.trans (d.plane_le_seed.trans (d.seed_le.trans d.chosen.le_sylow))
  have hPJ : V₁ ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hPT) (hPT.trans le_sup_right)
    (hJH.trans d.first_normalizer.le)
  have hJ : J ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T
    (d.counterexample.qtke.evenCharacteristic T)
    ⟨(fun he => hP (bot_unique (he ▸ hPJ))),fun _ ht =>
      (show (T : Subgroup G) ≤ J from le_sup_right) ht⟩
  exact Diagonal.contradiction_of_core_decomposition (K.map G₁.subtype) (sourceOne L T V₁) T
    hnG hpK ordinary_point_residual_twoPerfect b.center_eq_bot b.outer_two
    hJ b.not_le (b.residual_fixes hnG) b.core_decomposition b.core_disjoint b.core_commutator

/-- Feed the actual block geometry into the full ordinary source entry,
discharging plane noncentrality before invoking the abelian-span theorem. -/
theorem original_six_selected_source_inputs_of_blocks_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (blocks : ⁅G₁.pCoreIn 2,V₂⁆ = ⊥ → OrdinaryBlockSource d) :
    G₁ ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T G₁ M ∧
      IsMulCommutative (conjugateSpanBy V G₁) ∧
      ∀ H ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T G₁ M,
        (Chapter13.Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis ∧
        IsMulCommutative (Chapter13.Section08.Source.VH H V) ∧
        ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) H V,
          Odd c.path.length ∧
          Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c V₃ V₁ ∧
          ¬ ⁅c.Ugamma V₃,V⁆ ≤ c.Aone V₁ :=
  original_six_selected_source_inputs_at d hmax eL
    (original_six_plane_noncentral_of_diagonal_source_at d hmax eL h1332 escape
      (fun hc => ordinaryDiagonalSource_of_blocks d h1332 (blocks hc))) h1332 modules escape

omit d in
/-- Original module selection followed by the full source entry, with plane
noncentrality proved from the contrary-branch A₅ block geometry. -/
theorem exists_original_six_selected_source_inputs_of_blocks_at
    (hmax : Maximal (Counterexample T) L)
    (natural : ∃ V : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T L V) ∧
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      Chapter6.Source.IsConjugationModel L V
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)))
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (escape : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (blocks : ∀ (V V₁ V₂ V₃ : Subgroup G)
      (d : NaturalSetup T L V V₁ V₂ V₃ (normalizer (L : Set G)) (normalizer (V₁ : Set G))),
      ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ = ⊥ → OrdinaryBlockSource d) :
    ∃ V V₁ V₂ V₃ : Subgroup G,
      Nonempty (NaturalSetup T L V V₁ V₂ V₃
        (normalizer (L : Set G)) (normalizer (V₁ : Set G))) ∧
      normalizer (V₁ : Set G) ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T
        (normalizer (V₁ : Set G)) (normalizer (L : Set G)) ∧
      IsMulCommutative (conjugateSpanBy V (normalizer (V₁ : Set G))) ∧
      ∀ H ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T
          (normalizer (V₁ : Set G)) (normalizer (L : Set G)),
        (Chapter13.Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis ∧
        IsMulCommutative (Chapter13.Section08.Source.VH H V) ∧
        ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) H V,
          Odd c.path.length ∧
          Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c V₃ V₁ ∧
          ¬ ⁅c.Ugamma V₃,V⁆ ≤ c.Aone V₁ := by
  obtain ⟨V,⟨D⟩,hTV,hmodel⟩ := natural
  obtain ⟨V₁,V₂,V₃,⟨d⟩⟩ := exists_original_six_setup_of_chosen_module hmax.1 D hTV hmodel
  obtain ⟨eL,_,_⟩ := hmodel
  exact ⟨V,V₁,V₂,V₃,⟨d⟩,original_six_selected_source_inputs_of_blocks_at d hmax eL
    h1332 modules escape (blocks V V₁ V₂ V₃ d)⟩

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
