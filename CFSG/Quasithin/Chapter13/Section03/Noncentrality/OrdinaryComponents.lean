module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryReductions
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryParabolic
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.GuardedSource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.IntrinsicSource

/-!
# The actual ordinary component after 13.3.14(d)

The contrary plane-centralization assumption gives a nontrivial star core
by the original parabolic calculation. The first reductions and the full
V-span hypothesis supply every local premise of the guarded Fitting argument.
Its selected C-component moves the seed span: otherwise its two-perfectness
puts it in the solvable centralizing residual. The intrinsic omega-center
criterion therefore makes this very component a faithful local component.

The earlier 13.3.2 list and guarded 3.1.8(1) remain explicit. No F.9
hypothesis, abelian-span contradiction, or faithful action of the raw point
group is asserted. The output uses the original subtype and star projection.
Source: Aschbacher–Smith, 13.3.14(a–e), printed pp.891–892.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

private theorem ordinary_point_twoLocal : IsTwoLocal H := by
  rw [d.first_normalizer]
  exact ⟨P,(by intro he; have hh := d.line_card; simp [he] at hh),
    IsPGroup.of_card (n := 1) (by simpa using d.line_card),rfl⟩

private theorem ordinary_local_maximal
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    IsMaximalTwoLocal M ∧ (T : Subgroup G) ≤ M := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h1221.simpleQTKE T h1221.maximal_faithful.1
  have horb : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L _ L le_rfl d.normalizes_L)
      (le_componentOrbit L _)
  simpa only [horb,←d.local_normalizer] using
    And.intro hu.normalizer_maximal (le_sup_right.trans hu.normalizer_contains)

/-- Reduction (a) centralizes the original seed, as required in (c). -/
theorem ordinary_seed_centralized_of_plane_centralized
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥) : H.pCoreIn 2 ≤ centralizer (U : Set G) := by
  apply le_centralizer_iff.mp
  intro u hu
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp
    ((ordinary_reduction_a d hc).2 (le_conjugateSpanBy U H hu))).2.2

/-- Reduction (c) from the original contrary assumption. -/
theorem ordinary_reduction_c_of_plane_centralized
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥) :
    pCore 2 (star H (sourceOne L T P) (ordinary_point_residual_le_point d)) ≠ ⊥ :=
  ordinary_reduction_c d e (ordinary_seed_centralized_of_plane_centralized d hc)

/-- The actual post-(d) component, with all ordinary local inputs discharged. -/
theorem ordinary_moved_component_of_guarded_sources
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H))
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥) :
    ∃ K : Subgroup H, K.IsCComponent ∧
      IsComponent (Star H) (K.map (QuotientGroup.mk' (pCore 2 H))) ∧
      ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
        (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥ ∧
      (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H) ∧
      ⁅K,(sourceOne L T P).subgroupOf H⁆ = K ∧ IsQuasisimple (K ⧸ pCore 2 K) := by
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer ▸ d.line_stable
  have hHlocal := ordinary_point_twoLocal d
  have hH := Chapter1.twoLocal_mem_He_of_sylow_le T
    (d.counterexample.qtke.evenCharacteristic T) hHlocal hTH
  obtain ⟨hM,hTM⟩ := ordinary_local_maximal d h1221
  exact source_moved_component_of_guarded_sources d.counterexample.qtke T h1332 h318
    H (sourceOne L T P) (conjugateSpanBy U H) M hH hHlocal hTH
    (ordinary_point_residual_le_point d) (T_normalizes_one L T P d.line_stable)
    ordinary_point_residual_twoPerfect (ordinary_point_residual_quotient_card d e)
    hM hTM (ordinary_point_not_le_local d h1221 hV) (ordinary_reduction_a d hc).2
    (ordinary_reduction_b_of_nonabelian_full d e h1221 hV).2
    (ordinary_reduction_c_of_plane_centralized d e hc)

/-- Solvability in reduction (b) forces every actual component to move the seed span. -/
theorem ordinary_component_moves_seed_span
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H))
    (K : Subgroup H) (hK : K.IsCComponent) :
    ⁅conjugateSpanBy U H,K.map H.subtype⁆ ≠ ⊥ := by
  let B := K.map H.subtype
  have hB : Group.IsPerfect B := by
    let := hK.perfect
    exact Group.IsPerfect.map H.subtype
  have hpB : IsPPerfect 2 B := by
    let := hB
    intro N hn hp
    let := hn
    let := hp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  intro hz
  have hle := twoPerfect_le_centralizingResidual hpB
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  let := (ordinary_reduction_b_of_nonabelian_full d e h1221 hV).1
  have hs : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hle) (inclusion_injective hle)
  let := hs
  exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
    (K.equivMapOfInjective H.subtype H.subtype_injective).injective)

/-- The intrinsic omega-center criterion on the original component and subtype. -/
theorem ordinary_component_faithful
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H))
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) :
    K.map H.subtype ∈ MainForward.faithfulLocalComponents T := by
  have hm := ordinary_component_moves_seed_span d e h1221 hV K hK
  -- The intrinsic theorem applies to the whole span as well as to its seed.
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer ▸ d.line_stable
  have hlocal := ordinary_point_twoLocal d
  have hHe := Chapter1.twoLocal_mem_He_of_sylow_le T
    (d.counterexample.qtke.evenCharacteristic T) hlocal hTH
  have ha := (ordinary_reduction_a d hc).2
  have hω : (Stellmacher.omegaOneCenterAmbient (pCore 2 H)).map H.subtype =
      Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2) :=
    (Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective _).symm
  have hspanH : conjugateSpanBy U H ≤ H :=
    conjugateSpanBy_le (d.seed_le.trans (d.chosen.le_sylow.trans hTH)) H.le_normalizer
  have hUi : (conjugateSpanBy U H).subgroupOf H ≤
      Stellmacher.omegaOneCenterAmbient (pCore 2 H) := by
    intro u hu
    have hh := ha hu
    rw [←hω] at hh
    obtain ⟨v,hv,he⟩ := hh
    exact (H.subtype_injective he) ▸ hv
  have hmi : ⁅(conjugateSpanBy U H).subgroupOf H,K⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (fun A : Subgroup H => A.map H.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hspanH,Subgroup.map_bot] at hh
    exact hm hh
  exact (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mpr
    (source_component_faithful_local T H hTH (Chapter1.mem_H_of_isTwoLocal hlocal)
      hHe K _ hK hUi hmi)

/-- Literal consumer of reductions (a–d), producing the faithful component used in (e). -/
theorem ordinary_faithful_component_of_guarded_sources
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H))
    (hc : ⁅H.pCoreIn 2,E⁆ = ⊥) :
    ∃ K : Subgroup H, K.IsCComponent ∧
      IsComponent (Star H) (K.map (QuotientGroup.mk' (pCore 2 H))) ∧
      ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
        (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥ ∧
      (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H) ∧
      ⁅K,(sourceOne L T P).subgroupOf H⁆ = K ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ⁅conjugateSpanBy U H,K.map H.subtype⁆ ≠ ⊥ ∧
      K.map H.subtype ∈ MainForward.faithfulLocalComponents T := by
  obtain ⟨K,hK,hKs,hm,hn,hgen,hq⟩ :=
    ordinary_moved_component_of_guarded_sources d e h1221 h1332 h318 hV hc
  exact ⟨K,hK,hKs,hm,hn,hgen,hq,ordinary_component_moves_seed_span d e h1221 hV K hK,
    ordinary_component_faithful d e h1221 hV hc K hK⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
