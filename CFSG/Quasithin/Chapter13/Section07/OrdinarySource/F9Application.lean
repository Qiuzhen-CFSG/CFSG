module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.SourceElimination
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.Displacement
/-!
# The original F.9 application for an abelian seed closure

Plane noncentrality gives the marked parabolic centralizer and the two
commutator lifts required by F.9. The remaining F.9 fields follow from
Hypothesis12.2.1 and the actual escaping local subgroup. This application
also applies after13.5 has made the seed closure abelian.

For the full-span branch, nonabelianness itself puts the point normalizer
in the escaping family: otherwise the chosen TI subgroup makes it normalize
V, so its V-span is elementary abelian. This preserves the distinction
between the V₃-span and the full V-span.

Source: Aschbacher–Smith13.3.14,13.5.7 and13.7.1–2, printed pp.890–893,
917,935–936.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section07.NaturalAction
open Section05.ComponentReduction Section05.ComponentReduction.OriginalSix
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionQuotients.FiveSeed.BarMarking
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
include d e
/-- Original F.9 from actual plane noncentrality, valid also for an abelian seed closure. -/
theorem f9_of_plane_noncentral
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T D.Gz M)
    (hm : ⁅(normalizer (D.V₁:Set G)).pCoreIn 2,V₂⁆≠⊥) : D.Hypothesis := by
  have hc := Section05.AmbientSource.source_parabolic_centralizer d e h1221 hm
  have hTJ : (D.T : Subgroup G) ≤ D.H := le_sup_right.trans hH.1.2
  have hVJ : D.V ≤ D.H := d.chosen.le_sylow.trans hTJ
  have hHe : D.H ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 D.T
    (d.counterexample.qtke.evenCharacteristic D.T) ⟨hH.1.1,hTJ⟩
  have hchar : generalizedFitting D.H = pCore 2 D.H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp hHe)
  have hNL : normalizer (D.V : Set G) ≤ normalizer (D.L : Set G) :=
    h1221.normal_subgroup_normalizer_le d.normalizes_L
      (d.chosen.le_sylow.trans le_sup_right) d.chosen.ne_bot d.normalizes_V
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h1221.simpleQTKE D.T h1221.maximal_faithful.1
  have horb : componentOrbit D.L (D.T : Subgroup G) = D.L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer D.L D.T D.L le_rfl d.normalizes_L)
      (le_componentOrbit D.L D.T)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → D.LT ≤ N → N = M := by
    simpa only [ChapterF.Section09.Setup.LT,horb,←d.local_normalizer] using hu.normalizer_unique
  have hcontrol : D.H ⊓ normalizer (D.Vplus : Set G) ≤ normalizer (D.V : Set G) :=
    (inf_le_inf_right _ hH.2.1).trans ((Section05.PointAction.normalizer_intersection_source d hc).trans inf_le_right)
  have hL1 : D.L₁ = sourceOne D.L D.T D.V₁ := by
    have hh := normalizer_residual_eq D.L D.V₁ (D.T : Subgroup G) D.T.isPGroup' d.normalizes_L
    change sourceOne D.L D.T D.V₁ =
      (pResidual 2 (D.L ⊓ normalizer (D.V₁ : Set G) : Subgroup G)).map
        (D.L ⊓ normalizer (D.V₁ : Set G)).subtype at hh
    rw [←d.first_normalizer] at hh
    exact hh.symm
  have hP : D.V₁ ≤ D.Vplus := d.line_le_plane.trans d.plane_le_seed
  have hlt : D.V₁ < D.Vplus := lt_of_le_of_ne hP (by
    intro he
    have hec := congrArg (fun A : Subgroup G => Nat.card A) he
    rw [d.line_card,d.seed_card] at hec
    contradiction)
  have hq : IsQuasisimple (D.L ⧸ pCore 2 D.L) := IsQuasisimple.of_mulEquiv e.symm
  refine {
    elementary := d.chosen.elementary
    residual := (pResidual_eq_top_iff 2 D.L).mpr d.counterexample.local_component.2.1.2.1
    normalizes_L := d.normalizes_L
    characteristic_L := d.counterexample.local_component.2.1.2.2
    V_le_LT := d.chosen.le_sylow.trans le_sup_right
    reduced := source_reduced d
    sylow_centralizer := (Section05.PlaneGeometry.local_sylow_centralizer d hq).symm
    point_card := d.line_card
    normalizes_point := d.line_stable
    point_lt := hlt
    plus_le := d.seed_le
    H_centralizes := hH.2.1
    local_le := hH.1.2
    characteristic_H := hchar
    kernel_core := ?_
    local_normalizes := by
      rw [hL1]
      exact sup_le (Section07.ModelExclusions.point_residual_normalizes_seed d) d.seed_stable
    irreducible := by
      intro A hPA hAU hn
      rw [hL1] at hn
      exact source_seed_interval d A hPA hAU hn
    normalizer_control := le_inf inf_le_left hcontrol
    generated_core := sup_twoCore_eq_bot_of_unique D.LT D.H M huniq hH.2.2
    commutator_lifting := fun g hg hcomm hs hsecond =>
      Section05.QuadraticSource.ordinary_source_commutator_lifting d e hm g (hH.2.1 hg) hc hcomm hs hsecond }
  exact normalCore_point_kernel_le_of_index_two D.T D.L D.H M D.V D.Vplus D.V₁
    d.chosen.elementary.isPGroup d.seed_le (Section05.NormalBranch.SourceOrthogonal.seed_index d)
    hVJ hP hH.2.1 hcontrol hTJ d.normalizes_L
    (le_sup_left.trans d.normalizes_V) hNL (local_centralizer_le_core d e)
    huniq hH.2.2 hHe

omit e in
/-- Nonabelianness of the original full span forces the point normalizer
into the actual escaping family. -/
theorem point_normalizer_mem_Hz_of_nonabelian_full
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hU : ¬IsMulCommutative (conjugateSpanBy D.V D.Gz)) :
    D.Gz ∈ Section08.Source.Hz D.L₁ D.T D.Gz M := by
  have hPV := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hP : D.V₁≠⊥ := by
    intro he
    have hh := d.line_card
    rw [he,card_bot] at hh
    contradiction
  let : IsElementaryAbelian 2 D.V := d.chosen.elementary
  let : IsElementaryAbelian 2 D.V₁ := IsElementaryAbelian.of_le hPV
  have hcore : D.V₁≤D.Gz.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.V₁)
      (d.first_normalizer ▸ D.V₁.le_normalizer) (d.first_normalizer ▸ le_rfl)
  refine ⟨⟨?_,sup_le ?_ (d.first_normalizer ▸ d.line_stable)⟩,le_rfl,?_⟩
  · intro he
    exact hP (bot_unique (he ▸ hcore))
  · exact (map_subtype_le _).trans inf_le_right
  · intro hGM
    have hc : D.V⊓centralizer (D.L:Set G)=⊥ := by
      have hh := congrArg (Subgroup.map D.V.subtype)
        (Section07.ModelExclusions.NaturalModels.centralizer_bot d)
      change ((centralizer (D.L:Set G)).subgroupOf D.V).map D.V.subtype=
        (⊥:Subgroup D.V).map D.V.subtype at hh
      rwa [subgroupOf_map_subtype,Subgroup.map_bot,inf_comm] at hh
    have hTI := d.chosen.ti_of_centralizer_eq_bot h1221
      (fun X _ _=>ChapterA.Section02.theoremA_knownSimple (G:=X))
      (fun X _ _=>ChapterA.Section02.theoremC_knownSimple (G:=X)) hc
    have hGN : D.Gz≤normalizer (D.V:Set G) :=
      (le_inf (hGM.trans d.local_normalizer.le) d.first_normalizer.le).trans
        (inf_normalizer_le_of_trivial_intersections hTI hP hPV)
    have hUV : conjugateSpanBy D.V D.Gz≤D.V := conjugateSpanBy_le le_rfl hGN
    exact hU (le_centralizer_iff_isMulCommutative.mp
      (hUV.trans ((le_centralizer D.V).trans (centralizer_le hUV))))

/-- The original F.9 application and seed inputs needed by13.7.12 and13.7.4.
Only the earlier point-core/plane noncentrality remains explicit. -/
theorem inputs_of_plane_noncentral
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T D.Gz M)
    (hm : ⁅(normalizer (D.V₁:Set G)).pCoreIn 2,V₂⁆≠⊥) :
    D.Hypothesis ∧ IsMulCommutative D.UH ∧ ⁅D.Vplus,D.Gz.pCoreIn 2⁆≠⊥ := by
  exact ⟨f9_of_plane_noncentral d e h1221 hH hm,
    Section05.ComponentReduction.OriginalSix.source_closure_abelian d e h1221 hH,
    Section05.AmbientSource.source_seed_noncentral_of_plane_noncentral d hm⟩
end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
