module

public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.LinearThreeAt
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS

/-!
# HS source geometry at the original group and Sylow subgroup

The final D branch supplies its earlier naturality, structure and escape
implications at the original G,T. These proofs apply those implications
only there. The actual chosen module and flag give the two-group closure,
its Frattini subgroup, Sylow containment and the two center intersections.
No universal earlier theorem is inferred from a local implication.

This extension sits above Section04: LinearThreeAt already imports that
umbrella. The original universal geometry APIs remain unchanged. These
local versions feed the local-structure and literal type-HS consumers.
Source: Aschbacher--Smith 12.8.4, 12.8.10 and 14.3.28--32,
printed pp.851,853--854,1002--1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual seed-plane span and its center intersection, using only
naturality at this G,T. -/
theorem source_seed_geometry_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) :
    conjugateSpanBy (F.Vi 2) (F.Li L 1) = V ∧
    F.U = conjugateSpanBy (F.Vi 2) F.H ∧
    (¬ IsMulCommutative F.U → V ⊓ F.ZU = F.Vi 1) := by
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let := chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hirr := F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide)
  exact ⟨F.seed_eq_plane_span L (by decide) chosen.normalizes hirr,
    F.U_eq_plane_span L (by decide) chosen.normalizes hirr,
    F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide)⟩

/-- The original closure is a two-group with the marked Frattini subgroup. -/
theorem source_closure_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    let := chosen.elementary
    IsPGroup 2 F.U ∧ frattini F.U = (F.Vi 1).subgroupOf F.U ∧
      V ⊓ F.ZU = F.Vi 1 := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have hnat : 3 ≤ 3 → Nonempty (AmbientNaturalMarking L chosen.normalizes 3) :=
    fun _ => ⟨h.naturalMarking⟩
  refine ⟨F.localKernel_UH_isPGroup d.qtke L (normalizer (L : Set G)) F.H
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual hnat (h.point_mem_Hz_at F alternatives), ?_, ?_⟩
  · exact F.localKernel_frattini_eq_point d.qtke L (normalizer (L : Set G))
      (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes_at structural)
      h.residual hnat (h.flag_escape_at F alternatives) hne
  · let := F.localKernel_tilde_seed_elementary
    exact F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide) hne

/-- The same closure lies in the original Sylow subgroup. -/
theorem source_closure_le_sylow_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) : F.U ≤ (T : Subgroup G) := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  exact (F.localKernel_closure d.qtke L (normalizer (L : Set G)) F.H
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.point_mem_Hz_at F alternatives)).2.2.1.1


/-- Even characteristic identifies the actual point-centralizer core. -/
theorem source_fitting_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) : generalizedFitting F.H = pCore 2 F.H := by
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (F.localKernel_characteristicTwo d.qtke L (normalizer (L : Set G)) F.H
      (h.point_mem_Hz_at F alternatives))

/-- The original parabolic conjugator gives both literal center intersections. -/
theorem source_center_intersections_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.ZU ⊓ conjugate F.ZU g = Chapter12.Section08.centerIn (F.I₂ L) ∧
      F.ZU ⊓ conjugate F.U g = Chapter12.Section08.centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
      conjugate F.ZU g ⊓ F.U = Chapter12.Section08.centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨htwo, hphi, hc⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  obtain ⟨hcomm, hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives)
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  let B := F.localKernel_markedForm (by decide) htwo hphi hcomm
  obtain ⟨e, _, hgen, _⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural)
    hcomm hsquare hspan hne g hgP hgH
  have hi := F.parabolic_center_eq L g hgP hgen e (by decide) hc
    (F.binary_source_fixedSpace_pullback (by decide) L chosen.normalizes
      (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural)
      hcomm hsquare hspan hne g hgP hgH)
  refine ⟨hi, ?_, ?_⟩
  · rw [F.center_intersection (by decide) L chosen.normalizes hc hcomm
      (F.plane_centralizer_center B) g hgP hgH, hi]
  · rw [F.conjugate_center_intersection (by decide) L chosen.normalizes hc hcomm
      (F.plane_centralizer_center B) g hgP hgH, inf_comm (conjugate F.ZU g), hi]

/-- Centerlessness forces the nonextraspecial center to escape U. -/
theorem source_center_escape_of_centerless_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ¬ conjugate F.ZU g ≤ F.U := by
  let := chosen.elementary
  have hi := (source_center_intersections_at d earlier hq chosen structural alternatives
    F hne g hgP hgH).2.2
  rw [hI, bot_sup_eq] at hi
  intro hle
  rw [inf_eq_left.mpr hle] at hi
  exact hZ (Subgroup.map_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective hi)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
