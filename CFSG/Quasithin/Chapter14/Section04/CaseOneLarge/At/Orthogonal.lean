module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.At.Components
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Kernel
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Frame
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Generation
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Radicals
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Orbit
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Complement
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.TwoCore
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.SingularPoint
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.SeedPoint
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Selection
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.FlagAction
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Actions
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Interchange
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.CentralizerComparison
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Components
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.MovedModule
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ComponentOrbitExclusion

/-!
# Excluding the original orthogonal action at G,T

The natural seed constructs the original G.2.5 configuration and its
complement. The marked involution exchanges the two orthogonal factors;
centralizer comparison identifies the actual residual image. Its moved
module and selected diagonal component give the original source exclusion.

The earlier inputs are restricted to the original group and Sylow subgroup.
The universal APIs remain unchanged. The `import all` edges intentionally
reuse the private calculations of the corresponding source implementation;
only deductions depending on the earlier inputs are specialized here.
Source: Aschbacher--Smith, G.2.5, 14.4.7,9; printed pp.335--336,1009--1010; refs/quasithin.pdf.
-/

public noncomputable section

/- Specialization of CaseOneLarge/NaturalSetup.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem star_kernel_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    (ChapterG.Section02.LinearThree.starProjection (sourceSetup F L)).ker = pCore 2 L := by
  let H := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  ext l
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    ⟨l, mem_sup_left l.property⟩ = 1 ↔ l ∈ pCore 2 L
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have heLT (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
      x ∈ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) ↔ (x : G) ∈ centralizer (V : Set G) := by
    constructor
    · intro hx
      exact chosen.core_centralizes (mem_map_of_mem _ hx)
    · intro hx
      have hm := H.centralizer_LT_at structural ▸ (show (x : G) ∈
        (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) from ⟨x.property, hx⟩)
      obtain ⟨y, hy, he⟩ := hm
      exact (Subtype.ext he : y = x) ▸ hy
  rw [heLT]
  constructor
  · intro hl
    obtain ⟨y, hy, he⟩ := H.centralizer_L ▸
      (show (l : G) ∈ L ⊓ centralizer (V : Set G) from ⟨l.property, hl⟩)
    exact (Subtype.ext he : y = l) ▸ hy
  · intro hl
    have hm : (l : G) ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype hl
    exact (H.centralizer_L.ge hm).2

private noncomputable def starModel_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    (sourceSetup F L).star L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := by
  let π := ChapterG.Section02.LinearThree.starProjection (sourceSetup F L)
  let H := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let := chosen.elementary
  exact (QuotientGroup.quotientKerEquivOfSurjective π
    (ChapterG.Section02.LinearThree.starProjection_surjective _)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (G := L) (star_kernel_at d earlier hq chosen structural F)).trans
        (H.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm))

private theorem starModel_apply_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (l : L) :
    let := chosen.elementary
    BinaryLinear.OuterCyclic.slEquivLinear 3
      (starModel_at d earlier hq chosen structural F
        (ChapterG.Section02.LinearThree.starProjection (sourceSetup F L) l)) =
      (SourceAssembly.At.higherRankHypothesis d earlier hq chosen).naturalMarking.quotientEquiv
        (QuotientGroup.mk' (pCore 2 L) l) := by
  let π := ChapterG.Section02.LinearThree.starProjection (sourceSetup F L)
  let e := QuotientGroup.quotientKerEquivOfSurjective π
    (ChapterG.Section02.LinearThree.starProjection_surjective _)
  have he : e (QuotientGroup.mk' π.ker l) = π l := rfl
  have he' : e.symm (π l) = QuotientGroup.mk' π.ker l := e.symm_apply_eq.mpr he.symm
  dsimp only [starModel_at, MulEquiv.trans_apply]
  rw [he', QuotientGroup.mk'_apply, QuotientGroup.quotientMulEquivOfEq_mk, MulEquiv.apply_symm_apply]
  rfl

theorem source_frame_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (g : G)
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ l : G, l ∈ L ∧ l ∉ F.Li L 2 ⊔ (T : Subgroup G) ∧
      Disjoint (F.Vi 1) (conjugate (F.Vi 1) g) ∧
      F.Vi 1 ⊔ conjugate (F.Vi 1) g = F.Vi 2 ∧
      Disjoint (F.Vi 2) (conjugate (F.Vi 1) l) ∧
      F.Vi 2 ⊔ conjugate (F.Vi 1) l = V := by
  let := chosen.elementary
  let H := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hc₂ : Nat.card (F.Vi 2) = 4 := by simpa using F.card 2 (by decide)
  have hv : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hcG : Nat.card (conjugate (F.Vi 1) g) = 2 := by
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hc]
  have hneq : F.Vi 1 ≠ conjugate (F.Vi 1) g := by
    intro he
    exact hgH ((conjugate_eq_iff (F.Vi 1) g).mp he.symm)
  have hdis : Disjoint (F.Vi 1) (conjugate (F.Vi 1) g) :=
    disjoint_iff.mpr (inf_eq_bot_of_card_two_of_ne _ _ hc hcG hneq)
  have hg₂ : conjugate (F.Vi 1) g ≤ F.Vi 2 :=
    conjugate_le_of_normalizes (F.monotone (by decide)) g
      (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
  have hnorm : conjugate (F.Vi 1) g ≤ normalizer (F.Vi 1 : Set G) := by
    apply (show conjugate (F.Vi 1) g ≤ centralizer (F.Vi 1 : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro b hb a ha
    exact congrArg Subtype.val (mul_comm (⟨a, F.le_seed 1 ha⟩ : V)
      ⟨b, F.le_seed 2 (hg₂ hb)⟩)
  have hplane : F.Vi 1 ⊔ conjugate (F.Vi 1) g = F.Vi 2 := by
    apply eq_of_le_of_card_ge (sup_le (F.monotone (by decide)) hg₂)
    rw [card_sup_of_disjoint_of_normalizes _ _ hdis hnorm, hc, hcG, hc₂]
  obtain ⟨C, hCV, hC, hdC, hcC⟩ := complementary_point (F.Vi 2) (F.le_seed 2)
    (by rw [hc₂, hv]; decide)
  obtain ⟨l, hl, he⟩ := H.subspace_transitive (F.Vi 1) C (F.le_seed 1) hCV (hc.trans hC.symm)
  have hspan : F.Vi 2 ⊔ C = V :=
    eq_of_le_of_card_ge (sup_le (F.le_seed 2) hCV) (by rw [hcC, hc₂, hv])
  refine ⟨l, hl, ?_, hdis, hplane, he.symm ▸ hdC, he.symm ▸ hspan⟩
  intro hlP
  have hl₂ : l ∈ normalizer (F.Vi 2 : Set G) :=
    (sup_le ((F.Li_le L 2).trans inf_le_right) (F.invariant 2)) hlP
  have hle : C ≤ F.Vi 2 := he ▸
    conjugate_le_of_normalizes (F.monotone (by decide)) l hl₂
  have hz : C = ⊥ := (inf_eq_right.mpr hle).symm.trans hdC.eq_bot
  rw [hz, Subgroup.card_bot] at hC
  omega

theorem source_almostSpecial_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ l : G, l ∈ L ∧ l ∉ F.Li L 2 ⊔ (T : Subgroup G) ∧
      F.Vi 1 ⊔ conjugate (F.Vi 1) g = F.Vi 2 ∧
      Nonempty (ChapterG.Section02.LinearThree.Hypothesis
        (sourceSetup F L) (ZMod 2) 1 g l) := by
  let := chosen.elementary
  let H := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let D := sourceSetup F L
  let A := H.naturalMarking
  obtain ⟨h, hh, hhP, hdis, hplane, hdis', hspan⟩ := source_frame_at d earlier hq chosen F g hgP hgH
  rw [← hplane] at hdis' hspan
  have hpointspan : conjugateSpanBy (F.Vi 1) L = V := by
    apply le_antisymm (conjugateSpanBy_le (F.le_seed 1) chosen.normalizes)
    apply hspan.symm.le.trans
    apply sup_le (sup_le (le_conjugateSpanBy _ _) ?_) ?_
    · exact conjugate_le_of_normalizes (le_conjugateSpanBy _ _) g
        (le_normalizer_conjugateSpanBy _ _ hg)
    · exact conjugate_le_of_normalizes (le_conjugateSpanBy _ _) h
        (le_normalizer_conjugateSpanBy _ _ hh)
  have hUT := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
  have hUstar : D.star D.U ≠ ⊥ := by
    intro hz
    have hUC : F.U ≤ centralizer (V : Set G) := by
      intro x hx
      have hm : QuotientGroup.mk' (pCore 2 D.LT) ⟨x, mem_sup_right (hUT hx)⟩ ∈ D.star D.U :=
        mem_map_of_mem _ hx
      have hm1 := mem_bot.mp (hz ▸ hm)
      have hcore := (QuotientGroup.eq_one_iff _).mp hm1
      exact chosen.core_centralizes (mem_map_of_mem D.LT.subtype hcore)
    have hVZ : V ≤ F.ZU := by
      rw [ZU, centerIn_eq_inf_centralizer]
      exact le_inf (le_conjugateSpanBy V F.H) (le_centralizer_iff.mp hUC)
    exact hne (le_centralizer_iff_isMulCommutative.mp
      ((conjugateSpanBy_le hVZ F.H_normalizes_ZU).trans (centerIn_le_centralizer F.U)))
  refine ⟨h, hh, hhP, hplane, ⟨{
    setup := F.localKernel_hypothesis d.qtke L (normalizer (L : Set G)) F.H
      (by decide) chosen.le_sylow chosen.normalizes (H.sylow_normalizes_at structural)
      H.residual (fun _ => ⟨A⟩) (H.point_mem_Hz_at F alternatives)
    exponent_pos := by decide
    field_card := by norm_num
    span_eq := hpointspan
    model := starModel_at d earlier hq chosen structural F
    coordinates := A.coordinates.toAddEquiv.toMultiplicativeRight
    equivariant := ?_
    point := F.naturalFlagSpace A.coordinates 1
    point_dimension := F.naturalFlagSpace_finrank A.coordinates 1 (by decide)
    point_mem := fun v => (F.mem_naturalFlagSpace A.coordinates 1 v).symm
    star_U_ne_bot := hUstar
    g_mem := hg
    h_mem := hh
    points_disjoint := hdis
    third_disjoint := hdis'
    points_span := hspan }⟩⟩
  intro l v
  have he := congrArg (fun a : BinaryLinear.OuterCyclic.LinearGroup 3 =>
    a (A.coordinates (Additive.ofMul v)))
      (starModel_apply_at d earlier hq chosen structural F l)
  exact (A.equivariant l (Additive.ofMul v)).trans he.symm

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

end

/- Specialization of CaseOneLarge/NaturalSetup/Kernel.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

open LargerDimension.RankCore.GaschutzComplement

theorem source_frattini_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    (frattini F.U).map F.U.subtype ≤ F.Vi 1 := by
  obtain ⟨_, he, _⟩ := CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne
  rw [he, map_subgroupOf_eq_of_le (show F.Vi 1 ≤ F.U from
    (F.le_seed 1).trans (le_conjugateSpanBy V F.H))]

theorem source_span_eq_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugateSpan F.U L = L ⊔ F.U := by
  obtain ⟨l, _, _, _, ⟨B⟩⟩ := source_almostSpecial_at d earlier hq chosen structural alternatives
    F hne g hg hgP hgH
  have hUT := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
  have hphi := source_frattini_at d earlier hq chosen structural alternatives F hne
  exact (span_eq_of_g25 F g l B hUT hphi).trans (B.I_eq_LU hUT hphi)

theorem source_span_kernel_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (centralizer (V : Set G)).subgroupOf (conjugateSpan F.U L) =
      pCore 2 (conjugateSpan F.U L) := by
  obtain ⟨l, _, _, _, ⟨B⟩⟩ := source_almostSpecial_at d earlier hq chosen structural alternatives
    F hne g hg hgP hgH
  have hUT := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
  have hphi := source_frattini_at d earlier hq chosen structural alternatives F hne
  rw [span_eq_of_g25 F g l B hUT hphi]
  apply Subgroup.map_injective (ChapterG.Section02.LinearThree.I (sourceSetup F L) g l).subtype_injective
  change _ = ChapterG.Section02.LinearThree.S (sourceSetup F L) g l
  rw [subgroupOf_map_subtype, inf_comm, B.S_eq_star_kernel hUT hphi]
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact (SourceAssembly.At.higherRankHypothesis d earlier hq chosen).centralizer_LT_at structural ▸
      (show x ∈ (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) from
        ⟨B.I_le_LT hUT hx.1, hx.2⟩)
  · exact inf_le_inf_left _ chosen.core_centralizes

theorem source_span_core_normalizes_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    pCore 2 (conjugateSpan F.U L) ≤
      normalizer (F.U.subgroupOf (conjugateSpan F.U L) : Set (conjugateSpan F.U L)) := by
  obtain ⟨l, _, _, _, ⟨B⟩⟩ := source_almostSpecial_at d earlier hq chosen structural alternatives
    F hne g hg hgP hgH
  have hUT := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
  have hphi := source_frattini_at d earlier hq chosen structural alternatives F hne
  rw [span_eq_of_g25 F g l B hUT hphi]
  intro x hx
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  exact Subgroup.mem_normalizer_iff.mp (B.S_normalizes_U hUT hphi
    (mem_map_of_mem _ hx)) u.val

theorem source_span_normalizes_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugateSpan F.U L ≤ normalizer (V : Set G) := by
  rw [source_span_eq_at d earlier hq chosen structural alternatives F hne g hg hgP hgH]
  exact sup_le chosen.normalizes
    ((source_closure_le_sylow_at d earlier hq chosen structural alternatives F).trans
      (F.last ▸ F.invariant 3))

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

end

/- Specialization of CaseOneLarge/NaturalSetup/Frame.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module

open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension.RankCore.GaschutzComplement

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_natural_frame_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ l : G, l ∈ L ∧ l ∉ F.Li L 2 ⊔ (T : Subgroup G) ∧
      ∃ hIV : conjugateSpan F.U L ≤ normalizer (V : Set G),
        ∃ m : SourceNaturalFrame F.U V (F.Vi 1) (F.Vi 2) L g l hIV,
          Function.Surjective m.actor ∧
          m.actor.ker = pCore 2 (conjugateSpan F.U L) ∧
          (let I := conjugateSpan F.U L
           (pCore 2 I : Set I) =
             (F.U.subgroupOf I ⊓ pCore 2 I : Set I) *
             ((rightConjugate F.U g).subgroupOf I ⊓ pCore 2 I : Set I) *
             ((rightConjugate F.U l).subgroupOf I ⊓ pCore 2 I : Set I)) ∧
          ∀ x : conjugateSpan F.U L, (x : G) ∈ centralizer (F.Vi 2 : Set G) ↔
            m.actor x ∈ Matrix.PSL3Two.SourceFlag.planeFixer := by
  let := chosen.elementary
  obtain ⟨l,hl,hlP,hplane,⟨B⟩⟩ := source_almostSpecial_at d earlier hq chosen structural alternatives
    F hne g hg hgP hgH
  have hUT := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
  have hphi := source_frattini_at d earlier hq chosen structural alternatives F hne
  let D := sourceSetup F L
  let I := ChapterG.Section02.LinearThree.I D g l
  have hspan : conjugateSpan F.U L = I :=
    (source_span_eq_at d earlier hq chosen structural alternatives F hne g hg hgP hgH).trans
      (B.I_eq_LU hUT hphi).symm
  let hIV := source_span_normalizes_at d earlier hq chosen structural alternatives F hne g hg hgP hgH
  let eI := MulEquiv.subgroupCongr hspan
  let e := B.sourceCoreQuotientEquiv hUT hphi
  let a : conjugateSpan F.U L →* Matrix.PSL3Two.SL :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 I)).comp eI.toMonoidHom)
  let m : SourceNaturalAction (conjugateSpan F.U L) V hIV := {
    actor := a
    space := B.coordinates
    intertwines := fun x v => B.sourceCoreQuotientEquiv_equivariant hUT hphi (eI x) v }
  let pg := Matrix.PSL3.PointRadicalGeneration.conjugatePoint B.point
    (B.model (ChapterG.Section02.LinearThree.starProjection D ⟨g,hg⟩))
  let pl := Matrix.PSL3.PointRadicalGeneration.conjugatePoint B.point
    (B.model (ChapterG.Section02.LinearThree.starProjection D ⟨l,hl⟩))
  let frame : Matrix.SpecialLinearGroup.FrameGeometry.Frame (ZMod 2) := {
    point := ![pg,B.point,pl]
    dimension := by
      intro i
      fin_cases i
      · exact (Matrix.PSL3.PointRadicalGeneration.conjugatePoint_finrank _ _).trans B.point_dimension
      · exact B.point_dimension
      · exact (Matrix.PSL3.PointRadicalGeneration.conjugatePoint_finrank _ _).trans B.point_dimension
    disjoint := B.model_points_disjoint.symm
    third_disjoint := by
      change Disjoint (pg ⊔ B.point) pl
      rw [sup_comm pg B.point]
      exact B.model_third_disjoint
    span := by
      change (pg ⊔ B.point) ⊔ pl = ⊤
      rw [sup_comm pg B.point]
      exact B.model_points_span }
  obtain ⟨b,hb⟩ := frame.exists_basis
  have hb0 : Submodule.span (ZMod 2) {b 0} = pg := hb 0
  have hb1 : Submodule.span (ZMod 2) {b 1} = B.point := hb 1
  have hb2 : Submodule.span (ZMod 2) {b 2} = pl := hb 2
  let m' := changeCoordinates m b.equivFun
  have h0 (v : V) : (v : G) ∈ conjugate (F.Vi 1) g ↔
      b.equivFun (B.coordinates v).toAdd 1 = 0 ∧ b.equivFun (B.coordinates v).toAdd 2 = 0 := by
    have hp : (v : G) ∈ conjugate (F.Vi 1) g ↔ (B.coordinates v).toAdd ∈ pg :=
      (B.model_conjugatePoint_mem ⟨g,hg⟩ v).symm
    rw [hp, ← hb0, basis_line_mem]
    simp [Fin.forall_fin_succ]
  have h1 (v : V) : (v : G) ∈ F.Vi 1 ↔
      b.equivFun (B.coordinates v).toAdd 0 = 0 ∧ b.equivFun (B.coordinates v).toAdd 2 = 0 := by
    rw [B.point_mem, ← hb1, basis_line_mem]
    simp [Fin.forall_fin_succ]
  have h2 (v : V) : (v : G) ∈ conjugate (F.Vi 1) l ↔
      b.equivFun (B.coordinates v).toAdd 0 = 0 ∧ b.equivFun (B.coordinates v).toAdd 1 = 0 := by
    have hp : (v : G) ∈ conjugate (F.Vi 1) l ↔ (B.coordinates v).toAdd ∈ pl :=
      (B.model_conjugatePoint_mem ⟨l,hl⟩ v).symm
    rw [hp, ← hb2, basis_line_mem]
    simp [Fin.forall_fin_succ]
  have hAV := conjugate_le_of_normalizes (F.le_seed 1) g (chosen.normalizes hg)
  have hplane' (v : V) : (v : G) ∈ F.Vi 2 ↔ b.equivFun (B.coordinates v).toAdd 2 = 0 := by
    rw [← hplane, sup_comm]
    rw [space_sup_mem B.coordinates _ _ pg B.point hAV (F.le_seed 1)
      (fun v => (B.model_conjugatePoint_mem ⟨g,hg⟩ v).symm) B.point_mem,
      ← hb0, ← hb1, basis_plane_mem]
  let f : SourceNaturalFrame F.U V (F.Vi 1) (F.Vi 2) L g l hIV := {
    toSourceNaturalAction := m'
    plane_le := F.le_seed 2
    plane := hplane'
    line_g := h0
    line_one := h1
    line_l := h2
    line_g_le := hAV
    line_one_le := F.le_seed 1
    line_l_le := conjugate_le_of_normalizes (F.le_seed 1) l (chosen.normalizes hl) }
  refine ⟨l,hl,hlP,hIV,f, ?_, ?_, marked_span_core_product F g l B hUT hphi, ?_⟩
  · exact (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective.comp
      ((MulAut.conj b.equivFun).surjective.comp
        ((BinaryLinear.OuterCyclic.slEquivLinear 3).surjective.comp
          (e.surjective.comp ((QuotientGroup.mk'_surjective _).comp eI.surjective))))
  · exact f.toSourceNaturalAction.ker_eq.trans
      (source_span_kernel_at d earlier hq chosen structural alternatives F hne g hg hgP hgH)
  · exact f.toSourceNaturalAction.centralizer_plane (F.Vi 2) f.plane_le f.plane

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

end

/- Specialization of CaseOneLarge/Orthogonal/Generation.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_orthogonal_quotient_generation_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
    ⁅K,((F.X g).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H))⁆ = K := by
  let := chosen.elementary
  let := F.U_normal
  have hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let : K.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let X := ((F.X g).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let a := sourceAction F hk
  have models : RankCore.ActionAlternative.{u} a := .orthogonal κ e he
  have hf := source_fixed_space_of_marked_action_at d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH models
  obtain ⟨_,hx,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  have hqX : X.map q.toMonoidHom = F.terminalDot (F.X g) := by
    rw [map_map]
    rfl
  have hfix : fixedSpace a.representation X = Submodule.span (ZMod 2) {v} := by
    change fixedSpace (F.terminalRepresentation.comp q.toMonoidHom) X = _
    rw [fixedSpace_comp_map,hqX,hf,hline]
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  let E : Additive F.Uhat ≃ₗ[ZMod 2] Binary.V := e.trans Binary.binaryCoordinates
  have hm (k : K) (w : Additive F.Uhat) : E (a.representation k w) = Binary.action (κm k) (E w) := by
    change Binary.binaryCoordinates (e (a.representation k w)) = _
    rw [he]
    obtain ⟨b,hb⟩ := elementaryEquiv.surjective (κ k)
    have hb' : κm k = b := by
      change elementaryEquiv.symm (κ k) = b
      rw [← hb,elementaryEquiv.symm_apply_apply]
    rw [← hb,hb']
    exact toOrthogonal_coordinates b (e w)
  exact Binary.commutator_eq_of_fixed_line a.representation K X κm E hm v hyp.point_ne_zero hfix

theorem source_orthogonal_residual_generation_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    conjugate ((pResidual 2 F.H).map F.H.subtype) g =
      ⁅conjugate ((pResidual 2 F.H).map F.H.subtype) g,F.W⁆ := by
  let := chosen.elementary
  let := F.U_normal
  let a := earlierGeometry_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  have hgen := source_orthogonal_quotient_generation_at d earlier hq chosen structural alternatives
    F hne hZ g⁻¹ ((F.P L).inv_mem hgP) (fun h => hgH (inv_mem_iff.mp h)) κ e he
  rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)] at hgen
  have hs := RankCore.CentralizerGeometry.ModelGeneration.star_generation_transport F.H F.W g hgen
  have hW : F.W ≤ conjugate F.H g := by
    change RankCore.CentralizerGeometry.W F.U (F.Vi 2) ≤
      RankCore.CentralizerGeometry.conjugate F.H g
    rw [a.H_eq_centralizer,RankCore.CentralizerGeometry.conjugate_centralizer]
    exact inf_le_right.trans (centralizer_le a.conjugate_line_le_plane)
  change RankCore.CentralizerGeometry.conjugate ((pResidual 2 F.H).map F.H.subtype) g =
    ⁅RankCore.CentralizerGeometry.conjugate ((pResidual 2 F.H).map F.H.subtype) g,F.W⁆
  rw [RankCore.CentralizerGeometry.conjugate_residual]
  exact RankCore.CentralizerGeometry.ambient_residual_generation _ _ hW hs

theorem source_orthogonal_centralizer_trivial_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    let D := conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G)
    conjugate ((pResidual 2 F.H).map F.H.subtype) g ≤ centralizer (D : Set G) ∧
      D ⊓ centralizer (L : Set G) = ⊥ := by
  let := chosen.elementary
  let := F.U_normal
  let a := earlierGeometry_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  let D := conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G)
  let K := (pResidual 2 F.H).map F.H.subtype
  let M := normalizer (L : Set G)
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have hgen := source_orthogonal_residual_generation_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he
  have models : RankCore.ActionAlternative.{u} (sourceAction F
      (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)) := .orthogonal κ e he
  have hDW := (source_centralizer_bounds_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH models).2.2
  have hHD : conjugate F.H g ≤ normalizer (D : Set G) :=
    RankCore.CentralizerGeometry.relative_centralizer_normalized _ _
      (RankCore.CentralizerGeometry.conjugate_normalizes F.H F.U g a.normalizes)
  have hKD : conjugate K g ≤ centralizer (D : Set G) := by
    rw [hgen]
    exact RankCore.CentralizerGeometry.commutator_centralizes_of_normalizes _ _ _
      ((map_mono (map_subtype_le _)).trans hHD) hDW
  have hjoin : L ⊔ conjugate (T : Subgroup G) g = L ⊔ (T : Subgroup G) := by
    have hh := RankCore.CentralizerGeometry.conjugate_eq_self (L ⊔ (T : Subgroup G))
      ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hg))
    rw [RankCore.CentralizerGeometry.conjugate,Subgroup.map_sup] at hh
    change RankCore.CentralizerGeometry.conjugate L g ⊔
      RankCore.CentralizerGeometry.conjugate (T : Subgroup G) g = _ at hh
    rwa [RankCore.CentralizerGeometry.conjugate_eq_self L (L.le_normalizer hg)] at hh
  have hTL : conjugate (T : Subgroup G) g ≤ normalizer (L : Set G) := by
    have hh := RankCore.CentralizerGeometry.conjugate_normalizes (T : Subgroup G) L g
      (h.sylow_normalizes_at structural)
    rwa [RankCore.CentralizerGeometry.conjugate_eq_self L (L.le_normalizer hg)] at hh
  have hKM : ¬ conjugate K g ≤ M := by
    intro hh
    have hK : K ≤ M := by
      have hi : RankCore.CentralizerGeometry.conjugate
          (RankCore.CentralizerGeometry.conjugate K g) g⁻¹ ≤
          RankCore.CentralizerGeometry.conjugate M g⁻¹ := map_mono hh
      rwa [RankCore.CentralizerGeometry.conjugate_conjugate,mul_inv_cancel,
        RankCore.CentralizerGeometry.conjugate_one,
        RankCore.CentralizerGeometry.conjugate_eq_self M
          (M.le_normalizer (M.inv_mem (L.le_normalizer hg)))] at hi
    have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
    have hs : K ⊔ (T : Subgroup G) = F.H := by
      have hh := congrArg (Subgroup.map F.H.subtype)
        (pResidual_sup_sylow_eq_top (T.subtype hTH))
      rwa [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
        ← MonoidHom.range_eq_map,range_subtype] at hh
    exact h.flag_escape_at F alternatives (hs ▸ sup_le hK (h.sylow_normalizes_at structural))
  have hu : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ conjugate (T : Subgroup G) g ≤ N → N = M := by
    intro N hN hLN
    rw [hjoin] at hLN
    exact Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
      show N ∈ {P : Subgroup G | IsMaximalTwoLocal P ∧ L ⊔ (T : Subgroup G) ≤ P}
        from ⟨hN,hLN⟩)
  exact ⟨hKD, RankCore.CentralizerGeometry.relative_centralizer_eq_bot_of_unique
    (conjugate K g) D L (conjugate (T : Subgroup G) g) M a.D_isTwoGroup hKD
    ((map_mono (F.invariant 1)).trans hHD) hTL hu hKM⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

end

/- Specialization of CaseOneLarge/NaturalSetup/Radicals.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module

open scoped IsMulCommutative Pointwise commutatorElement

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension.RankCore.GaschutzComplement

open Matrix.PSL3Two

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_radical_card_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {hIV : conjugateSpan F.U L ≤ normalizer (V : Set G)}
    (m : SourceNaturalAction (conjugateSpan F.U L) V hIV) :
    Nat.card ((F.U.subgroupOf (conjugateSpan F.U L)).map m.actor) = 4 := by
  obtain ⟨l,_,_,_,⟨B⟩⟩ := source_almostSpecial_at d earlier hq chosen structural alternatives F hne g hg hgP hgH
  have hUT := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
  have hphi := source_frattini_at d earlier hq chosen structural alternatives F hne
  let D := sourceSetup F L
  let I := conjugateSpan F.U L
  have hILT : I ≤ D.LT := by
    rw [show I = L ⊔ F.U from source_span_eq_at d earlier hq chosen structural alternatives F hne g hg hgP hgH]
    exact sup_le le_sup_left (hUT.trans le_sup_right)
  let q : I →* D.Star := (QuotientGroup.mk' (pCore 2 D.LT)).comp (inclusion hILT)
  have hk : q.ker = m.actor.ker := by
    rw [m.ker_eq]
    ext x
    change QuotientGroup.mk' (pCore 2 D.LT) (inclusion hILT x) = 1 ↔
      (x : G) ∈ centralizer (V : Set G)
    rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact chosen.core_centralizes (mem_map_of_mem D.LT.subtype hx)
    · intro hx
      have hm := (SourceAssembly.At.higherRankHypothesis d earlier hq chosen).centralizer_LT_at structural ▸
        (show (x : G) ∈ (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) from ⟨hILT x.property,hx⟩)
      obtain ⟨y,hy,he⟩ := hm
      exact (show y = inclusion hILT x from Subtype.ext he) ▸ hy
  have hmap : (F.U.subgroupOf I).map q = D.star D.U := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨inclusion hILT x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,le_conjugateSpan F.U L hx⟩,hx,rfl⟩
  calc
    Nat.card ((F.U.subgroupOf I).map m.actor) = Nat.card ((F.U.subgroupOf I).map q) := by
      rw [← relIndex_ker,← relIndex_ker,hk]
    _ = 4 := by rw [hmap,B.card_star_U hUT hphi]; norm_num

theorem source_radical_images_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (l : G) {hIV : conjugateSpan F.U L ≤ normalizer (V : Set G)}
    (m : SourceNaturalFrame F.U V (F.Vi 1) (F.Vi 2) L g l hIV) :
    (F.U.subgroupOf (conjugateSpan F.U L)).map m.actor = SourceFlag.secondRadical ∧
    ((rightConjugate F.U g).subgroupOf (conjugateSpan F.U L)).map m.actor =
      MarkedAutomorphisms.pointV := by
  obtain ⟨l',_,_,_,⟨B⟩⟩ := source_almostSpecial_at d earlier hq chosen structural alternatives F hne g hg hgP hgH
  have hUT := source_closure_le_sylow_at d earlier hq chosen structural alternatives F
  have hphi := source_frattini_at d earlier hq chosen structural alternatives F hne
  have hmove : ⁅F.U,V⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact (B.commutator_V_U_eq_point hUT hphi).le
  have hfix : F.U ≤ centralizer (F.Vi 1 : Set G) := B.setup.U_le_centralizer_point
  have hmoveg : ⁅rightConjugate F.U g,V⁆ ≤ rightConjugate (F.Vi 1) g := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hmove
    rw [map_commutator] at hh
    have hv : V.map (MulAut.conj g⁻¹).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (V : Set G)).inv_mem (chosen.normalizes hg))
    rwa [hv] at hh
  have hfixg : rightConjugate F.U g ≤ centralizer (rightConjugate (F.Vi 1) g : Set G) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hfix
    rwa [LargerDimension.RankCore.CentralizerGeometry.centralizer_map] at hh
  have hle : (F.U.subgroupOf (conjugateSpan F.U L)).map m.actor ≤ SourceFlag.secondRadical := by
    rintro _ ⟨x,hx,rfl⟩
    apply secondRadical_of_action
    · obtain ⟨v,hv⟩ := m.space.surjective (Multiplicative.ofAdd ![0,1,0])
      have hvl : (v : G) ∈ F.Vi 1 := (m.line_one v).mpr (by simp [hv])
      have he := (m.toSourceNaturalAction.fixes_iff x v).mpr (hfix hx _ hvl)
      simpa [hv] using he
    · intro w
      obtain ⟨v,hv⟩ := m.space.surjective (Multiplicative.ofAdd w)
      obtain ⟨hp,he⟩ := action_displacement m.toSourceNaturalAction F.U (F.Vi 1) hmove x hx v
      have hh := (m.line_one _).mp hp
      simpa only [he,hv,toAdd_ofAdd] using hh
  have hleg : ((rightConjugate F.U g).subgroupOf (conjugateSpan F.U L)).map m.actor ≤ MarkedAutomorphisms.pointV := by
    rintro _ ⟨x,hx,rfl⟩
    apply pointV_of_action
    · obtain ⟨v,hv⟩ := m.space.surjective (Multiplicative.ofAdd ![1,0,0])
      have hvl : (v : G) ∈ rightConjugate (F.Vi 1) g := (m.line_g v).mpr (by simp [hv])
      have he := (m.toSourceNaturalAction.fixes_iff x v).mpr (hfixg hx _ hvl)
      simpa [hv] using he
    · intro w
      obtain ⟨v,hv⟩ := m.space.surjective (Multiplicative.ofAdd w)
      obtain ⟨hp,he⟩ := action_displacement m.toSourceNaturalAction _ _ hmoveg x hx v
      have hh := (m.line_g _).mp hp
      simpa only [he,hv,toAdd_ofAdd] using hh
  have hc := source_radical_card_at d earlier hq chosen structural alternatives F hne g hg hgP hgH m.toSourceNaturalAction
  have hc₂ : Nat.card SourceFlag.secondRadical = 4 := by
    rw [SourceFlag.secondRadical,MulEquiv.toMonoidHom_eq_coe,comap_equiv_eq_map_symm,card_map_of_injective (MulAut.conj (Bruhat.perm 2)).symm.injective]
    exact MarkedAutomorphisms.card_pointV
  have hLI : L ≤ conjugateSpan F.U L := by
    rw [source_span_eq_at d earlier hq chosen structural alternatives F hne g hg hgP hgH]
    exact le_sup_left
  have hcg : Nat.card (((rightConjugate F.U g).subgroupOf (conjugateSpan F.U L)).map m.actor) = 4 := by
    rw [map_rightConjugate (le_conjugateSpan F.U L) ⟨g,hLI hg⟩ m.actor,
      card_map_of_injective (MulAut.conj (m.actor ⟨g,hLI hg⟩)⁻¹).injective]
    exact hc
  exact ⟨eq_of_le_of_card_ge hle (by omega),
    eq_of_le_of_card_ge hleg (by rw [hcg,MarkedAutomorphisms.card_pointV])⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

end

/- Specialization of CaseOneLarge/NaturalSetup/Orbit.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension.RankCore.GaschutzComplement

open Matrix.PSL3.PointRadicalGeneration

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_point_orbits_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∀ x ∈ L, conjugate (F.Vi 1) x = conjugate (F.Vi 1) g ∨
      ∃ t ∈ L, t ∈ conjugate F.H g ∧ conjugate (F.Vi 1) x = conjugate (F.Vi 1) t := by
  obtain ⟨l,_,_,_,⟨B⟩⟩ := source_almostSpecial_at d earlier hq chosen structural alternatives F hne g hg hgP hgH
  let D := sourceSetup F L
  let pg := conjugatePoint B.point (B.model (ChapterG.Section02.LinearThree.starProjection D ⟨g,hg⟩))
  have hpg : finrank (ZMod 2) pg = 1 := (conjugatePoint_finrank _ _).trans B.point_dimension
  have hAg : conjugate (F.Vi 1) g ≤ V := conjugate_le_of_normalizes (F.le_seed 1) g (chosen.normalizes hg)
  have hpgmem (v : V) : (v : G) ∈ conjugate (F.Vi 1) g ↔ (B.coordinates v).toAdd ∈ pg :=
    (B.model_conjugatePoint_mem ⟨g,hg⟩ v).symm
  have hneP : B.point ≠ pg := by
    intro he
    have hd : Disjoint B.point pg := B.model_points_disjoint
    rw [← he] at hd
    have hz : B.point = ⊥ := disjoint_self.mp hd
    have hc := B.point_dimension
    rw [hz,finrank_bot] at hc
    contradiction
  intro x hx
  by_cases heq : conjugate (F.Vi 1) x = conjugate (F.Vi 1) g
  · exact Or.inl heq
  apply Or.inr
  let px := conjugatePoint B.point (B.model (ChapterG.Section02.LinearThree.starProjection D ⟨x,hx⟩))
  have hpx : finrank (ZMod 2) px = 1 := (conjugatePoint_finrank _ _).trans B.point_dimension
  have hAx : conjugate (F.Vi 1) x ≤ V := conjugate_le_of_normalizes (F.le_seed 1) x (chosen.normalizes hx)
  have hpxmem (v : V) : (v : G) ∈ conjugate (F.Vi 1) x ↔ (B.coordinates v).toAdd ∈ px :=
    (B.model_conjugatePoint_mem ⟨x,hx⟩ v).symm
  have hneX : px ≠ pg := by
    intro he
    apply heq
    apply le_antisymm
    · intro v hv
      exact (hpgmem ⟨v,hAx hv⟩).mpr (he ▸ (hpxmem ⟨v,hAx hv⟩).mp hv)
    · intro v hv
      exact (hpxmem ⟨v,hAg hv⟩).mpr (he ▸ (hpgmem ⟨v,hAg hv⟩).mp hv)
  obtain ⟨a,haX,haG⟩ := Matrix.SpecialLinearGroup.FrameGeometry.exists_point_pair_map
    px pg B.point pg hpx hpg B.point_dimension hpg hneX hneP
  obtain ⟨t,ht⟩ := (ChapterG.Section02.LinearThree.starProjection_surjective D) (B.model.symm a)
  have hta : B.model (ChapterG.Section02.LinearThree.starProjection D t) = a := by
    rw [ht,B.model.apply_symm_apply]
  have hAt : conjugate (F.Vi 1) t = conjugate (F.Vi 1) x :=
    coordinate_conjugate F g l B (F.Vi 1) (conjugate (F.Vi 1) x) (F.le_seed 1) hAx
      B.point px B.point_mem hpxmem t (by rw [hta]; exact haX)
  have hGt : conjugate (conjugate (F.Vi 1) g) t = conjugate (F.Vi 1) g :=
    coordinate_conjugate F g l B _ _ hAg hAg pg pg hpgmem hpgmem t (by rw [hta]; exact haG)
  refine ⟨t,t.property,?_,hAt.symm⟩
  have hn := (conjugate_eq_iff (conjugate (F.Vi 1) g) t).mp hGt
  change (t : G) ∈ (normalizer (F.Vi 1 : Set G)).map (MulAut.conj g⁻¹).toMonoidHom
  rw [map_equiv_normalizer_eq]
  exact hn

theorem source_seed_fixed_bot_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨l,_,_,_,⟨B⟩⟩ := source_almostSpecial_at d earlier hq chosen structural alternatives F hne g hg hgP hgH
  have hn : L ≤ normalizer (V ⊓ centralizer (L : Set G) : Set G) :=
    (le_centralizer_iff.mp (show V ⊓ centralizer (L : Set G) ≤ centralizer (L : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  rcases B.irreducible (V ⊓ centralizer (L : Set G)) inf_le_left hn with hb | he
  · exact hb
  · have he' : V ⊓ centralizer (L : Set G) = V := he
    have hc : V ≤ centralizer (L : Set G) := he'.ge.trans inf_le_right
    exact (hgH ((Subgroup.centralizer_le_normalizer (F.Vi 1 : Set G))
      ((le_centralizer_iff.mp hc).trans (centralizer_le (F.le_seed 1)) hg))).elim

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

end

/- Specialization of CaseOneLarge/NaturalSetup/Complement.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module

open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension CoreGeometry

open LargerDimension.RankCore.GaschutzComplement

universe u w

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_natural_complement_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (models : letI := chosen.elementary
      letI := F.U_normal
      RankCore.ActionAlternative.{w} (sourceAction F
        (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ))) :
    conjugateCentralizer F.H F.U g = rightConjugate (F.Vi 1) g ⊔
      (conjugateCentralizer F.H F.U g ⊓ centralizer (L : Set G)) := by
  let := chosen.elementary
  let := F.U_normal
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).1
  let a := earlierGeometry_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  have hpoints := source_point_orbits_at d earlier hq chosen structural alternatives F hne g hg hgP hgH
  obtain ⟨_,hDU,hDW⟩ := source_centralizer_bounds_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH models
  have hb := RankCore.CentralizerGeometry.symmetric_commutator_bounds F.H F.U (F.Vi 1) L V g
    a.H_eq_normalizer a.normalizes (F.le_seed 1) chosen.normalizes
    (fun x hx => (hpoints x hx).imp_right (fun ⟨t,_,ht,he⟩ => ⟨t,ht,he⟩)) hDU
  have hW : F.U ⊓ centralizer (F.Vi 2 : Set G) ≤ centralizer (conjugateCentralizer F.H F.U g : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hDW)
  have hfixed := RankCore.CentralizerGeometry.symmetric_fixed_centralizers F.H F.U (F.Vi 1) (F.Vi 2) L V g
    a.H_eq_normalizer a.normalizes (F.le_seed 2) chosen.normalizes hpoints hDW
  obtain ⟨l,hl,hlP,hIV,m,_,_,hcore,_⟩ := source_natural_frame_at d earlier hq chosen structural alternatives F hne g hg hgP hgH
  obtain ⟨hU,hUg⟩ := source_radical_images_at d earlier hq chosen structural alternatives F hne g hg hgP hgH l m
  have hVU : V ≤ rightConjugate F.U g := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (le_conjugateSpanBy V F.H)
    change RankCore.CentralizerGeometry.conjugate V g ≤ rightConjugate F.U g at hh
    rwa [RankCore.CentralizerGeometry.conjugate_eq_self V (chosen.normalizes hg)] at hh
  have hcenter : rightConjugate F.U g ⊓ centralizer (rightConjugate F.U g : Set G) = rightConjugate (F.Vi 1) g := by
    have hc : F.U ⊓ centralizer (F.U : Set G) = F.Vi 1 := (centerIn_eq_inf_centralizer F.U).symm.trans hZ
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hc
    rwa [map_inf _ _ _ (MulAut.conj g⁻¹).injective,RankCore.CentralizerGeometry.centralizer_map] at hh
  exact (source_complement_of_g25 F.H F.U V (F.Vi 1) (F.Vi 2) L g l hg hl
    (source_span_eq_at d earlier hq chosen structural alternatives F hne g hg hgP hgH) hIV
    (fun v hv => elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv) hVU
    (map_mono F.U_le_H) (fun x hx => (hb x hx).1) (fun x hx => (hb x hx).2)
    hW (hfixed l hl) (source_seed_fixed_bot_at d earlier hq chosen structural alternatives F hne g hg hgP hgH)
    hcenter m hU hUg (source_span_kernel_at d earlier hq chosen structural alternatives F hne g hg hgP hgH)
    (source_span_core_normalizes_at d earlier hq chosen structural alternatives F hne g hg hgP hgH) hcore).1

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup

end

/- Specialization of CaseOneLarge/Orthogonal/TwoCore.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_orthogonal_twoCore_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    (conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G) = conjugate (F.Vi 1) g) ∧
      F.H.pCoreIn 2 = F.U := by
  let := chosen.elementary
  let := F.U_normal
  have models : RankCore.ActionAlternative.{u} (sourceAction F
    (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)) := .orthogonal κ e he
  have hd := NaturalSetup.source_natural_complement_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH models
  have hz := (source_orthogonal_centralizer_trivial_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH κ e he).2
  have hd' : conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G) = conjugate (F.Vi 1) g := by
    change conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G) =
      conjugate (F.Vi 1) g ⊔ ((conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G)) ⊓ centralizer (L : Set G)) at hd
    simpa only [hz,sup_bot_eq] using hd
  refine ⟨hd',?_⟩
  have hcore := source_conjugate_core_product_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  have hline : conjugate (F.Vi 1) g ≤ conjugate F.U g :=
    map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  rw [hd',sup_eq_left.mpr hline] at hcore
  exact Subgroup.map_injective (MulAut.conj g⁻¹).injective hcore

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

end

/- Specialization of CaseOneLarge/Orthogonal/SingularPoint.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

theorem source_orthogonal_singular_point_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    F.H.pCoreIn 2 = F.U ∧ Nat.card V = 8 ∧ Nat.card (hatSpace F V) = 4 ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ hs : MulAut.conj g⁻¹ z ∈ F.U,
          let v := e (hatElement F ⟨MulAut.conj g⁻¹ z,hs⟩)
          MulAut.conj g⁻¹ z ∈ F.Vi 2 ∧ v ≠ 0 ∧
          formD 2 Binary.F v = 0 ∧
          (hatSpace F (F.Vi 2)).map e.toLinearMap = Submodule.span (ZMod 2) {v} ∧
          ∀ w ∈ Submodule.span Binary.F {v}, formD 2 Binary.F w = 0 := by
  let := chosen.elementary
  have hc := (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).2.2
  have hv : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hhat : Nat.card (hatSpace F V) = 4 := by
    have hm := card_hatImage_mul_card_inf F V (le_conjugateSpanBy V F.H)
    rw [hc,F.card 1 (by decide),hv] at hm
    rw [card_hatSpace]
    omega
  refine ⟨(source_orthogonal_twoCore_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he).2,hv,hhat,?_⟩
  obtain ⟨z,hz,hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzo : orderOf z = 2 := by
    rw [← Nat.card_zpowers,← hzp]
    exact F.card 1 (by decide)
  refine ⟨z,hzo,hzp,F.H_eq_centralizer (by decide) z hzp,?_⟩
  exact singular_original_generator F
    (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)
    hc g z (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
    (chosen.normalizes hg) hgH hz hzp κ e he

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

end

/- Specialization of CaseOneLarge/Orthogonal/SeedPoint.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Matrix Subgroup Module Representation Representation.BinaryOffender

open ClassicalOrthogonal.FourPlusMatrix

open scoped Pointwise


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

theorem source_orthogonal_seed_point_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    F.H.pCoreIn 2 = F.U ∧ Nat.card V = 8 ∧ Nat.card (hatSpace F V) = 4 ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ hs : MulAut.conj g⁻¹ z ∈ F.U,
          let v := e (hatElement F ⟨MulAut.conj g⁻¹ z,hs⟩)
          MulAut.conj g⁻¹ z ∈ F.Vi 2 ∧ v ≠ 0 ∧
          formD 2 Binary.F v = 0 ∧
          (hatSpace F (F.Vi 2)).map e.toLinearMap = Submodule.span (ZMod 2) {v} ∧
          (hatSpace F V).map e.toLinearMap =
            (Submodule.span Binary.F {v}).restrictScalars (ZMod 2) ∧
          ∀ w ∈ (hatSpace F V).map e.toLinearMap, formD 2 Binary.F w = 0 := by
  let := chosen.elementary
  obtain ⟨hcore,hV,hhat,z,hzo,hzp,hH,hs,hs₂,hv0,hqv,hline,hsing⟩ :=
    source_orthogonal_singular_point_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  have hd : finrank (ZMod 2) (hatSpace F V) = 2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := hatSpace F V)
    rw [hhat,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh).symm
  have hn : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H) ≤
      normalizer (V.subgroupOf F.H : Set F.H) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro v
    have htV : (t : G) ∈ normalizer (V : Set G) := by simpa [F.last] using F.invariant 3 ht
    exact mem_normalizer_iff.mp htV (v : G)
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let : K.Normal := (inferInstance : (pResidual 2 F.H).Normal).map _ (QuotientGroup.mk'_surjective _)
  have hp := orthogonal_plane_field_line (sourceAction F hk) K κ e he
    (T.subtype (F.invariant 1)) (V.subgroupOf F.H) hn
    (by rw [sourceAction_image]; exact hd)
    (hatElement F ⟨MulAut.conj g⁻¹ z,hs⟩)
    (by rw [sourceAction_image]; exact ⟨⟨_,hs⟩,F.le_seed 2 hs₂,rfl⟩)
    (fun hh => hv0 (hh ▸ e.map_zero))
  rw [sourceAction_image] at hp
  refine ⟨hcore,hV,hhat,z,hzo,hzp,hH,hs,hs₂,hv0,hqv,hline,hp,?_⟩
  intro w hw
  rw [hp] at hw
  exact hsing w hw

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

end

/- Specialization of CaseOneLarge/Orthogonal/Selection.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Matrix Subgroup Module Representation Representation.BinaryOffender

open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal


open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension CoreGeometry

open scoped IsMulCommutative commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

theorem source_orthogonal_hyperplane_selection_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    F.H.pCoreIn 2 = F.U ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ k : G, k ∈ (pResidual 2 F.H).map F.H.subtype ∧
          MulAut.conj k⁻¹ (MulAut.conj g⁻¹ z) ∈ F.W ∧
          MulAut.conj k⁻¹ (MulAut.conj g⁻¹ z) ∉ centralizer (V : Set G) := by
  let := chosen.elementary
  obtain ⟨hcore,_,_,z,hzo,hzp,hH,hs,hs₂,hv0,hqv,hline,hpoint,_⟩ :=
    source_orthogonal_seed_point_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  let D := sourceAction F hk
  let C := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  have hcomm := (source_commutator_squares_at d earlier hq chosen structural alternatives F).1
  let B := F.localKernel_markedForm (by decide) C.two C.frattini_point hcomm
  let E := e.trans Binary.binaryCoordinates
  let b := LinearMap.BilinForm.congr E B.form
  let s : F.U := ⟨MulAut.conj g⁻¹ z,hs⟩
  let v := hatElement F s
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  have hm (k : K) (w : Additive F.Uhat) :
      E (D.representation k w) = Binary.action (κm k) (E w) := by
    change Binary.binaryCoordinates (e (D.representation k w)) = _
    rw [he]
    obtain ⟨a,ha⟩ := elementaryEquiv.surjective (κ k)
    have hκ : κm k = a := by
      change elementaryEquiv.symm (κ k) = a
      rw [←ha,elementaryEquiv.symm_apply_apply]
    rw [←ha,hκ]
    exact toOrthogonal_coordinates a (e w)
  have hinv (h : F.H) (w y : Additive F.Uhat) :
      B.form (D.representation (QuotientGroup.mk' (pCore 2 F.H) h) w)
        (D.representation (QuotientGroup.mk' (pCore 2 F.H) h) y) = B.form w y := by
    change F.uhatBilinearForm (by decide) C.two C.frattini_point
      (Additive.ofMul (F.uhatAction h w.toMul)) (Additive.ofMul (F.uhatAction h y.toMul)) = _
    rw [F.uhatBilinearForm_apply,F.uhatCommutator_invariant (by decide) C.two C.frattini_point]
    rfl
  have hbi (a : Binary.G) (w y : Binary.V) :
      b (Binary.action a w) (Binary.action a y) = b w y := by
    obtain ⟨k,rfl⟩ := κm.surjective a
    obtain ⟨h,hh,heq⟩ := k.property
    have hew : E.symm (Binary.action (κm k) w) = D.representation k (E.symm w) := by
      apply E.injective
      rw [E.apply_symm_apply,hm,E.apply_symm_apply]
    have hey : E.symm (Binary.action (κm k) y) = D.representation k (E.symm y) := by
      apply E.injective
      rw [E.apply_symm_apply,hm,E.apply_symm_apply]
    change B.form (E.symm _) (E.symm _) = B.form (E.symm w) (E.symm y)
    rw [hew,hey,←heq]
    exact hinv h _ _
  obtain ⟨a,ha,c,hc⟩ := matrix_selection b (B.nondegenerate.congr E) hbi (E v)
    (fun hh => hv0 (Binary.binaryCoordinates.injective (hh.trans Binary.binaryCoordinates.map_zero.symm)))
    ((coordinates_det (e v)).trans hqv)
  obtain ⟨k,hka⟩ := κm.surjective a
  obtain ⟨h,hh,heq⟩ := k.property
  let t : F.U := subgroupOfEquivOfLe F.U_le_H
    (MulAut.conjNormal h ((subgroupOfEquivOfLe F.U_le_H).symm s))
  have ht : E (hatElement F t) = Binary.action a (E v) := by
    rw [←hka,←hm,←heq]
    exact congrArg E (D.conjugation h ((subgroupOfEquivOfLe F.U_le_H).symm s))
  have hzero : B.form v (hatElement F t) = 0 := by
    rw [←ht] at ha
    change B.form (E.symm (E v)) (E.symm (E (hatElement F t))) = 0 at ha
    simpa only [E.symm_apply_apply] using ha
  have htW : (t : G) ∈ F.W := by
    refine ⟨t.property,?_⟩
    apply (hat_orthogonal_iff F B.form (commutator_form_zero F hcomm B)
      (F.Vi 2) ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) t).mp
    intro w hw
    have hew : e w ∈ Submodule.span (ZMod 2) {e v} := hline ▸ ⟨w,hw,rfl⟩
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hew
    have hrw : r • v = w := e.injective (by simpa using hr)
    rw [←hrw]
    simp [hzero]
  have htV : (t : G) ∉ centralizer (V : Set G) := by
    intro hh
    have ho := (hat_orthogonal_iff F B.form (commutator_form_zero F hcomm B)
      V (le_conjugateSpanBy V F.H) t).mpr hh
    have hmemb : E.symm (c • E v) ∈ hatSpace F V := by
      have hec : e (E.symm (c • E v)) = c • e v := by
        apply Binary.binaryCoordinates.injective
        change E (E.symm (c • E v)) = coordinates (c • e v)
        rw [E.apply_symm_apply,map_smul]
        rfl
      have hh : c • e v ∈ (hatSpace F V).map e.toLinearMap := by
        rw [hpoint]
        exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
      rw [←hec] at hh
      obtain ⟨w,hw,hew⟩ := hh
      exact e.injective hew ▸ hw
    apply hc
    rw [←ht]
    change B.form (E.symm (c • E v)) (E.symm (E (hatElement F t))) = 0
    rw [E.symm_apply_apply]
    exact ho _ hmemb
  refine ⟨hcore,z,hzo,hzp,hH,(h:G)⁻¹,?_,?_,?_⟩
  · exact mem_map_of_mem _ ((pResidual 2 F.H).inv_mem hh)
  · change (h:G) * (MulAut.conj g⁻¹ z) * (h:G)⁻¹ ∈ F.W at htW
    simpa only [inv_inv,MulAut.conj_apply] using htW
  · change (h:G) * (MulAut.conj g⁻¹ z) * (h:G)⁻¹ ∉ centralizer (V : Set G) at htV
    simpa only [inv_inv,MulAut.conj_apply] using htV

theorem source_orthogonal_selected_involution_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    F.H.pCoreIn 2 = F.U ∧
      ∃ z : G, orderOf z = 2 ∧ F.Vi 1 = zpowers z ∧
        F.H = centralizer ({z} : Set G) ∧
        ∃ k : G, k ∈ (pResidual 2 F.H).map F.H.subtype ∧
          let x := g*k*g
          let i := MulAut.conj x⁻¹ z
          orderOf i = 2 ∧ i ∈ F.X g ∧ i ∈ T ∧ i ∉ F.U ∧
          i ∉ centralizer (V : Set G) := by
  let := chosen.elementary
  obtain ⟨hcore,z,hzo,hzp,hH,k,hk,hsW,hsV⟩ :=
    source_orthogonal_hyperplane_selection_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  let s := MulAut.conj k⁻¹ (MulAut.conj g⁻¹ z)
  let i := MulAut.conj (g*k*g)⁻¹ z
  have hi : i = MulAut.conj g⁻¹ s := by
    simp [i,s,MulAut.conj_apply,mul_assoc]
  have hiX : i ∈ F.X g := hi ▸ mem_map_of_mem _ hsW
  have hiV : i ∉ centralizer (V : Set G) := by
    intro hv
    apply hsV
    have hnorm := normalizer_le_normalizer_centralizer V (chosen.normalizes hg)
    have hh := (mem_normalizer_iff.mp hnorm i).mp hv
    change s ∈ centralizer (V : Set G)
    simpa [hi,MulAut.conj_apply,mul_assoc] using hh
  let C := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [C.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU :=
    disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) C.seed_center g
      (chosen.normalizes hg) hgH)
  let : IsElementaryAbelian 2 (F.E g) := F.E_elementary (by decide) g C.two hPhi hdis
  have hVE : V ≤ F.E g := (F.parabolic_seed_geometry L chosen.normalizes g hgP).1
  have hiU : i ∉ F.U := by
    intro hu
    have hiW : i ∈ F.W := ⟨hu,F.X_le_plane_centralizer g
      (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hiX⟩
    have hiE : i ∈ F.E g := ⟨hiW,hiX⟩
    apply hiV
    intro v hv
    exact congrArg Subtype.val (mul_comm (⟨v,hVE hv⟩ : F.E g) ⟨i,hiE⟩)
  refine ⟨hcore,z,hzo,hzp,hH,k,hk,?_,hiX,?_,hiU,hiV⟩
  · simpa only [MulEquiv.orderOf_eq] using hzo
  · exact (source_extraspecial_data_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH).1.Wg_le_T hiX

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

end

/- Specialization of CaseOneLarge/Orthogonal/FlagAction.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_orthogonal_flag_reduction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    let D := conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G)
    Nat.card F.U = 512 ∧ 512 ≤ Nat.card T ∧
      fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
      conjugate (F.H.pCoreIn 2) g = conjugate F.U g ⊔ D ∧
      D ≤ F.H.pCoreIn 2 ∧ ⁅D,F.U⁆ ≤ F.Vi 1 ∧ ⁅D,F.W⁆ = ⊥ := by
  let := chosen.elementary
  let := F.U_normal
  have hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  have models : RankCore.ActionAlternative.{u} (sourceAction F hk) := .orthogonal κ e he
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 :=
    (e.trans Binary.binaryCoordinates).finrank_eq.trans Binary.finrank_binary
  have hz := (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).1.center_order_p
  have hc : Nat.card F.U = 512 := by
    have hqcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    rw [Nat.card_zmod,hd] at hqcard
    rw [card_eq_card_quotient_mul_card_subgroup (center F.U),hz]
    change Nat.card (Additive F.Uhat) * 2 = 512
    norm_num only [hqcard]
  have hT : 512 ≤ Nat.card T := by
    rw [← hc]
    exact Nat.card_le_card_of_injective _
      (inclusion_injective (source_closure_le_sylow_at d earlier hq chosen structural alternatives F))
  exact ⟨hc,hT,source_fixed_space_of_marked_action_at d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH models,
    source_conjugate_core_product_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH,
    source_centralizer_bounds_at d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH models⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

end

/- Specialization of CaseOneLarge/Orthogonal/Actions.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Orthogonal CoreGeometry

open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

def source_orthogonal_action_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    ExchangedModel.CaseThreeAction F.H F.U := by
  let := chosen.elementary
  have hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  have hcore := (source_orthogonal_twoCore_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he).2
  let D := sourceAction F hk
  let E := e.trans Binary.binaryCoordinates
  let ρ : Representation (ZMod 2) F.H Binary.V :=
    E.conjRingEquiv.toMonoidHom.comp (D.representation.comp (QuotientGroup.mk' (pCore 2 F.H)))
  let a : F.H →* (Binary.V ≃ₗ[ZMod 2] Binary.V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Binary.V).toMonoidHom.comp ρ.asGroupHom
  have ha (h : F.H) (v : Additive F.Uhat) :
      a h (E v) = E (D.representation (QuotientGroup.mk' (pCore 2 F.H) h) v) := by
    change E (D.representation (QuotientGroup.mk' (pCore 2 F.H) h) (E.symm (E v))) = _
    rw [E.symm_apply_apply]
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  have hm (k : K) (w : Additive F.Uhat) :
      E (D.representation k w) = Binary.action (κm k) (E w) := by
    change Binary.binaryCoordinates (e (D.representation k w)) = _
    rw [he]
    obtain ⟨b,hb⟩ := elementaryEquiv.surjective (κ k)
    have hb' : κm k = b := by
      change elementaryEquiv.symm (κ k) = b
      rw [←hb,elementaryEquiv.symm_apply_apply]
    rw [←hb,hb']
    exact toOrthogonal_coordinates b (e w)
  refine {
    normalizes := le_normalizer_conjugateSpanBy V F.H
    coordinates := matrixCoordinates F E
    action := a
    equivariant := ?_
    kernel := ?_
    components := pResidual 2 F.H
    components_normal := inferInstance
    outer_two := isPGroup_quotient_pResidual 2
    components_image := ?_ }
  · intro h u
    change E (Additive.ofMul (QuotientGroup.mk' (center F.U) _)) = a h (E (hatElement F u))
    rw [ha]
    exact congrArg (fun v => E (Additive.ofMul v)) (F.terminalHatAction_apply_mk h u).symm
  · intro h hh
    have hz : F.terminalHatAction h = 1 := by
      apply MulEquiv.ext
      intro v
      apply E.injective
      have hv := ha h (Additive.ofMul v)
      rw [show a h = 1 from hh] at hv
      exact hv.symm
    have hh' : h ∈ pCore 2 F.H := hk ▸ hz
    have hu : (h:G) ∈ F.H.pCoreIn 2 := mem_map_of_mem F.H.subtype hh'
    rwa [hcore] at hu
  · apply le_antisymm
    · rintro _ ⟨h,hh,rfl⟩
      let k : K := ⟨QuotientGroup.mk' (pCore 2 F.H) h,mem_map_of_mem _ hh⟩
      refine ⟨κm k,?_⟩
      apply LinearEquiv.ext
      intro v
      obtain ⟨w,rfl⟩ := E.surjective v
      exact (hm k w).symm.trans (ha h w).symm
    · rintro _ ⟨b,rfl⟩
      obtain ⟨k,hk⟩ := κm.surjective b
      obtain ⟨h,hh,hq⟩ := k.property
      refine ⟨h,hh,?_⟩
      apply LinearEquiv.ext
      intro v
      obtain ⟨w,rfl⟩ := E.surjective v
      rw [ha]
      change E (D.representation (QuotientGroup.mk' (pCore 2 F.H) h) w) = Binary.action b (E w)
      rw [hq,hm,hk]

theorem source_orthogonal_moved_rank_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (i : F.H) (hiX : (i:G) ∈ F.X g)
    (hiV : (i:G) ∉ centralizer (V : Set G)) (hio : orderOf (i:G) = 2) :
    let m := source_orthogonal_action_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
    finrank (ZMod 2) (LinearMap.range ((m.action i).toLinearMap - LinearMap.id)) = 4 ∧
      Nat.card (movedImage F.U (i:G)) = 16 := by
  let := chosen.elementary
  let m := source_orthogonal_action_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he
  let E := e.trans Binary.binaryCoordinates
  have ha (h : F.H) (w : Additive F.Uhat) :
      m.action h (E w) = E (Additive.ofMul (F.uhatAction h w.toMul)) := by
    change E (Additive.ofMul (F.uhatAction h (E.symm (E w)).toMul)) = _
    rw [E.symm_apply_apply]
  obtain ⟨_,_,_,z,_,_,_,hs,hs₂,_,_,_,hpoint,_⟩ :=
    source_orthogonal_seed_point_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  let s : F.U := ⟨MulAut.conj g⁻¹ z,hs⟩
  let v := hatElement F s
  have hiconj : F.uAction i s = s := by
    apply Subtype.ext
    change (i:G)*(s:G)*(i:G)⁻¹ = (s:G)
    rw [←F.X_le_plane_centralizer g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hiX s hs₂]
    exact mul_inv_cancel_right _ _
  have hfix : m.action i (E v) = E v := by
    rw [ha]
    change E (Additive.ofMul (F.uhatAction i (QuotientGroup.mk' (center F.U) s))) = _
    rw [F.uhatAction_apply_mk,hiconj]
    rfl
  have hnlin : ¬ ∀ (c : Binary.F) (w : Binary.V), m.action i (c • w) = c • m.action i w := by
    intro hlin
    have hfixV (w : Additive F.Uhat) (hw : w ∈ hatSpace F V) :
        F.uhatAction i w.toMul = w.toMul := by
      have hw' : e w ∈ (Submodule.span Binary.F {e v}).restrictScalars (ZMod 2) :=
        hpoint ▸ ⟨w,hw,rfl⟩
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw'
      have hwE : E w = c • E v := by
        change coordinates (e w) = c • coordinates (e v)
        rw [←hc,map_smul]
      apply Additive.ofMul.injective
      apply E.injective
      rw [←ha,hwE,hlin,hfix]
      exact hwE.symm
    let C := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
    have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU :=
      disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) C.seed_center g
        (chosen.normalizes hg) hgH)
    have hcomm := (source_commutator_squares_at d earlier hq chosen structural alternatives F).1
    have hVE : V ≤ F.E g := (F.parabolic_seed_geometry L chosen.normalizes g hgP).1
    apply hiV
    intro w hw
    let u : F.U := ⟨w,le_conjugateSpanBy V F.H hw⟩
    have hf := hfixV (hatElement F u) ⟨u,hw,rfl⟩
    change F.uhatAction i (QuotientGroup.mk' (center F.U) u) =
      QuotientGroup.mk' (center F.U) u at hf
    rw [F.uhatAction_apply_mk] at hf
    have hc : F.uAction i u / u ∈ center F.U := QuotientGroup.eq_iff_div_mem.mp hf
    have hd : ((F.uAction i u / u : F.U) : G) = ⁅(i:G),w⁆ := by
      change ((i:G)*w*(i:G)⁻¹)/w = _
      simp only [commutatorElement_def,div_eq_mul_inv]
    have hz : ⁅(i:G),w⁆ ∈ F.ZU := ⟨_,hc,hd⟩
    have hr := commutator_X_E_le_conjugate_point F g hcomm
      (commutator_mem_commutator hiX (hVE hw))
    have hone := mem_bot.mp (hdis.le_bot ⟨hr,hz⟩)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  obtain ⟨σ,hσ⟩ := Binary.normalizer_semilinear (m.action i) (m.action_normalizes i)
  have hσne : ∃ c : Binary.F, σ c ≠ c := by
    by_contra! h
    apply hnlin
    simpa only [h] using hσ
  have hl := NaturalTensor.finrank_le_twice_operatorFixedCodim
    (m.action i).toLinearMap σ.toRingHom hσne hσ
  rw [Binary.finrank_binary] at hl
  let t := m.action i
  let f : Binary.V →ₗ[ZMod 2] Binary.V := t.toLinearMap - LinearMap.id
  have ht : t ^ 2 = 1 := by
    rw [←map_pow]
    have hi2 : i ^ 2 = 1 := Subtype.ext (hio ▸ pow_orderOf_eq_one (i:G))
    rw [hi2,map_one]
  have hle : f.range ≤ f.ker := by
    rintro _ ⟨w,rfl⟩
    change t (t w - w) - (t w - w) = 0
    have htw : t (t w) = w := LinearEquiv.congr_fun ht w
    rw [map_sub,htw]
    apply sub_eq_zero.mpr
    exact sub_eq_sub_iff_add_eq_add.mpr (by
      apply Matrix.ext
      intro j k
      exact (CharTwo.add_self_eq_zero (w j k)).trans
        (CharTwo.add_self_eq_zero (t w j k)).symm)
  have hr := f.finrank_range_add_finrank_ker
  have hu := Submodule.finrank_mono hle
  rw [Binary.finrank_binary] at hr
  have hdim : finrank (ZMod 2) f.range = 4 := by
    change 8 ≤ 2 * finrank (ZMod 2) f.range at hl
    omega
  refine ⟨hdim,?_⟩
  rw [←m.subspace_card (movedImage F.U (i:G)),m.subspace_moved i hio,
    Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,hdim]
  norm_num

def source_orthogonal_exchanged_action_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (z x : G) (hH : F.H = centralizer ({z} : Set G)) :
    ExchangedModel.CaseThreeAction
      (centralizer ({conjugateElement z x} : Set G)) (conjugateCore F.U x) := by
  let m := source_orthogonal_action_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he
  have a := transport_orthogonal_action F.H F.U m (MulAut.conj x⁻¹)
  change ExchangedModel.CaseThreeAction (conjugateCore F.H x) (conjugateCore F.U x) at a
  rwa [hH,LargerDimension.Orthogonal.conjugate_centralizer] at a

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

end

/- Specialization of CaseOneLarge/Orthogonal/Interchange.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative commutatorElement

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

private theorem source_orthogonal_selected_swaps_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (i : F.H) (hiX : (i:G) ∈ F.X g)
    (hiV : (i:G) ∉ centralizer (V : Set G)) :
    Binary.InvolutionResidual.SwapsFactors
      (sourceStarAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)
        e (QuotientGroup.mk' (pCore 2 F.H) i)) := by
  let := chosen.elementary
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  let D := sourceAction F hk
  let E := e.trans Binary.binaryCoordinates
  let f := sourceStarAction F hk e
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let : K.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let X := ((F.X g).subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  have hqX : X.map q.toMonoidHom = F.terminalDot (F.X g) := by
    rw [Subgroup.map_map]
    rfl
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  have hm (k : K) (w : Additive F.Uhat) : E (D.representation k w) = Binary.action (κm k) (E w) := by
    change Binary.binaryCoordinates (e (D.representation k w)) = _
    rw [he]
    obtain ⟨b,hb⟩ := elementaryEquiv.surjective (κ k)
    have hb' : κm k = b := by
      change elementaryEquiv.symm (κ k) = b
      rw [←hb,elementaryEquiv.symm_apply_apply]
    rw [←hb,hb']
    exact toOrthogonal_coordinates b (e w)
  have himage : K.map f = Binary.linearAction.range := by
    apply le_antisymm
    · rintro _ ⟨k,hk',rfl⟩
      refine ⟨κm ⟨k,hk'⟩,?_⟩
      apply LinearEquiv.ext
      intro w
      obtain ⟨v,rfl⟩ := E.surjective w
      rw [Binary.linearAction_apply,sourceStarAction_apply]
      exact (hm ⟨k,hk'⟩ v).symm
    · rintro _ ⟨b,rfl⟩
      obtain ⟨k,hk'⟩ := κm.surjective b
      refine ⟨k,k.property,?_⟩
      apply LinearEquiv.ext
      intro w
      obtain ⟨v,rfl⟩ := E.surjective w
      rw [Binary.linearAction_apply,sourceStarAction_apply,hm,hk']
  obtain ⟨_,_,_,z,_,_,_,hs,hs₂,hv0,hvs,hline,hpoint,_⟩ :=
    source_orthogonal_seed_point_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  let s : F.U := ⟨MulAut.conj g⁻¹ z,hs⟩
  let v := hatElement F s
  have hv : v ≠ 0 := by
    intro h
    apply hv0
    change e v = 0
    rw [h,map_zero]
  have hline' : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) := by
    apply Submodule.map_injective_of_injective e.injective
    rw [hline,Submodule.map_span]
    simp only [Set.image_singleton]
    rfl
  obtain ⟨hXP,hXN⟩ := source_actor_normal_in_point_stabilizer_at d earlier hq chosen
    structural alternatives F hne hZ g hgP hgH v hv hline'
  have hNX := (normal_subgroupOf_iff_le_normalizer hXP).mp hXN
  have hXtwo : IsPGroup 2 X := by
    obtain ⟨_,heX,_,_,_⟩ := source_terminal_hypothesis_at F d earlier hq chosen
      structural alternatives hne g hgP hgH
    let := heX
    have htwo : IsPGroup 2 (X.map q.toMonoidHom) := by
      rw [hqX]
      exact IsElementaryAbelian.isPGroup 2 _
    exact htwo.of_injective (q.subgroupMap X).toMonoidHom (q.subgroupMap X).injective
  have hn (a : F.H ⧸ pCore 2 F.H) (ha : f a (E v) = E v) :
      a ∈ normalizer (X : Set (F.H ⧸ pCore 2 F.H)) := by
    have hvfix : F.terminalRepresentation (q a) v = v := by
      apply E.injective
      exact (sourceStarAction_apply F hk e a v).symm.trans ha
    have hh := hNX hvfix
    rw [←hqX,←map_equiv_normalizer_eq] at hh
    obtain ⟨b,hb,heq⟩ := hh
    exact q.injective heq ▸ hb
  have hfix : f (QuotientGroup.mk' (pCore 2 F.H) i) (E v) = E v := by
    rw [sourceStarAction_apply]
    have hiconj : F.uAction i s = s := by
      apply Subtype.ext
      change (i:G)*(s:G)*(i:G)⁻¹ = (s:G)
      rw [←F.X_le_plane_centralizer g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hiX s hs₂]
      exact mul_inv_cancel_right _ _
    change E (Additive.ofMul (F.uhatAction i (QuotientGroup.mk' (center F.U) s))) = _
    rw [F.uhatAction_apply_mk,hiconj]
    rfl
  have hmove : ∃ c : Binary.F,
      f (QuotientGroup.mk' (pCore 2 F.H) i) (c • E v) ≠ c • E v := by
    by_contra! hfixline
    have hfixV (w : Additive F.Uhat) (hw : w ∈ hatSpace F V) : F.uhatAction i w.toMul = w.toMul := by
      have hw' : e w ∈ (Submodule.span Binary.F {e v}).restrictScalars (ZMod 2) := hpoint ▸ ⟨w,hw,rfl⟩
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw'
      have hwE : E w = c • E v := by
        change coordinates (e w) = c • coordinates (e v)
        rw [←hc,map_smul]
      apply Additive.ofMul.injective
      apply E.injective
      change E (D.representation (QuotientGroup.mk' (pCore 2 F.H) i) w) = E w
      rw [←sourceStarAction_apply,hwE,hfixline]
    let C := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
    have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU :=
      disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) C.seed_center g (chosen.normalizes hg) hgH)
    have hcomm := (source_commutator_squares_at d earlier hq chosen structural alternatives F).1
    have hVE : V ≤ F.E g := (F.parabolic_seed_geometry L chosen.normalizes g hgP).1
    apply hiV
    intro w hw
    let u : F.U := ⟨w,le_conjugateSpanBy V F.H hw⟩
    have hf := hfixV (hatElement F u) ⟨u,hw,rfl⟩
    change F.uhatAction i (QuotientGroup.mk' (center F.U) u) = QuotientGroup.mk' (center F.U) u at hf
    rw [F.uhatAction_apply_mk] at hf
    have hc : F.uAction i u / u ∈ center F.U := QuotientGroup.eq_iff_div_mem.mp hf
    have hd : ((F.uAction i u / u : F.U) : G) = ⁅(i:G),w⁆ := by
      change ((i:G)*w*(i:G)⁻¹)/w = _
      simp only [commutatorElement_def,div_eq_mul_inv]
    have hz : ⁅(i:G),w⁆ ∈ F.ZU := ⟨_,hc,hd⟩
    have hr := commutator_X_E_le_conjugate_point F g hcomm (commutator_mem_commutator hiX (hVE hw))
    have hone := mem_bot.mp (hdis.le_bot ⟨hr,hz⟩)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  apply PointExchange.swaps_of_point_normal_two f (sourceStarAction_injective F hk e)
    (himage ▸ map_le_range f K) X hXtwo (E v)
    (fun hh => hv (E.injective (hh.trans E.map_zero.symm)))
    ((coordinates_det (e v)).trans hvs) hn (QuotientGroup.mk' (pCore 2 F.H) i)
    (mem_map_of_mem _ hiX) hfix ?_ hmove
  rw [←himage]
  exact K.le_normalizer_map f (mem_map_of_mem f (by rw [normalizer_eq_top]; trivial))

theorem source_orthogonal_action_swaps_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (i : F.H) (hiX : (i:G) ∈ F.X g)
    (hiV : (i:G) ∉ centralizer (V : Set G)) :
    Binary.InvolutionResidual.SwapsFactors
      ((source_orthogonal_action_at d earlier hq chosen structural alternatives
        F hne hZ g hg hgP hgH κ e he).action i) := by
  exact source_orthogonal_selected_swaps_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he i hiX hiV

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

end

/- Specialization of CaseOneLarge/Orthogonal/CentralizerComparison.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Orthogonal CoreGeometry

open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

theorem source_orthogonal_centralizer_comparison_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (z : G) (hzp : F.Vi 1 = zpowers z)
    (hH : F.H = centralizer ({z} : Set G))
    (i : F.H) (hiX : (i:G) ∈ F.X g)
    (hiV : (i:G) ∉ centralizer (V : Set G)) (hio : orderOf (i:G) = 2) :
    ((commutatorPreimage F.H (zpowers (i:G)) (zpowers z)).subgroupOf F.H).map
      (QuotientGroup.mk' (pCore 2 F.H)) =
      centralizer ({QuotientGroup.mk' (pCore 2 F.H) i} : Set (F.H ⧸ pCore 2 F.H)) := by
  let m := source_orthogonal_action_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he
  have hcore := (source_orthogonal_twoCore_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he).2
  have hHZ : F.H ≤ normalizer (zpowers z : Set G) := by
    rw [hH]
    simpa only [zpowers_eq_closure,centralizer_closure] using
      (centralizer_le_normalizer (zpowers z : Set G))
  exact centralizer_comparison_of_moved_rank F.H F.U m hcore z (hZ.trans hzp) hHZ i hio
    (source_orthogonal_moved_rank_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he i hiX hiV hio).1

theorem source_selected_contradiction_of_diagonal_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (z x : G) (hz : orderOf z = 2) (hzp : F.Vi 1 = zpowers z)
    (hH : F.H = centralizer ({z} : Set G))
    (hiT : conjugateElement z x ∈ T) (hout : conjugateElement z x ∉ F.U)
    (hiX : conjugateElement z x ∈ F.X g)
    (hiV : conjugateElement z x ∉ centralizer (V : Set G))
    (hKU : diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
      normalizer (F.U : Set G))
    (m : MovedCoreModel F.U
      (diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x))
      (conjugateElement z x) hKU)
    (components : QuotientModel.SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
        ⟨conjugateElement z x,(hH ▸ (show (T : Subgroup G) ≤ F.H from F.invariant 1)) hiT⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x)).subgroupOf
        (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) :
    False := by
  let := chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order_at d earlier hq chosen structural alternatives F hne hZ).1
  have hc := (source_orthogonal_twoCore_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he).2
  have hsize := (source_orthogonal_flag_reduction_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he).1
  have hi : orderOf (conjugateElement z x) = 2 := by
    simpa only [conjugateElement,MulEquiv.orderOf_eq] using hz
  have hcompare : ∀ hiH : conjugateElement z x ∈ F.H,
      ((commutatorPreimage F.H (zpowers (conjugateElement z x)) (zpowers z)).subgroupOf F.H).map
        (QuotientGroup.mk' (pCore 2 F.H)) =
        centralizer ({QuotientGroup.mk' (pCore 2 F.H) ⟨conjugateElement z x,hiH⟩} :
          Set (F.H ⧸ pCore 2 F.H)) := by
    intro hiH
    exact source_orthogonal_centralizer_comparison_at d earlier hq chosen
      structural alternatives F hne hZ g hg hgP hgH κ e he z hzp hH
      ⟨conjugateElement z x,hiH⟩ hiX hiV hi
  rw [hH] at hcompare
  exact source_selected_configuration_contradiction d.qtke F.U T z x hz
    (hZ.trans hzp) (hH ▸ hc) hsize (hH ▸ (show (T : Subgroup G) ≤ F.H from F.invariant 1)) hiT hout hKU m
    (source_orthogonal_exchanged_action_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he z x hH) components (hcompare _)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

end

/- Specialization of CaseOneLarge/Orthogonal/Components.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative commutatorElement

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Orthogonal CoreGeometry

open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

theorem source_orthogonal_selected_components_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (z : G) (hz : orderOf z = 2) (hzp : F.Vi 1 = zpowers z)
    (hH : F.H = centralizer ({z} : Set G))
    (i : F.H) (hiX : (i:G) ∈ F.X g)
    (hiV : (i:G) ∉ centralizer (V : Set G)) (hio : orderOf (i:G) = 2) :
    Nonempty (QuotientModel.SelectedComponentData (F.H ⧸ pCore 2 F.H)
      (QuotientGroup.mk' (pCore 2 F.H) i)
      (((diagonalResidual F.H (i:G)).subgroupOf F.H).map
        (QuotientGroup.mk' (pCore 2 F.H)))) := by
  let := chosen.elementary
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  let D := sourceAction F hk
  let E := e.trans Binary.binaryCoordinates
  let f := sourceStarAction F hk e
  let K := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let : K.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let κm : K ≃* Binary.G := κ.trans elementaryEquiv.symm
  have hm (k : K) (w : Additive F.Uhat) : E (D.representation k w) = Binary.action (κm k) (E w) := by
    change Binary.binaryCoordinates (e (D.representation k w)) = _
    rw [he]
    obtain ⟨b,hb⟩ := elementaryEquiv.surjective (κ k)
    have hb' : κm k = b := by
      change elementaryEquiv.symm (κ k) = b
      rw [←hb,elementaryEquiv.symm_apply_apply]
    rw [←hb,hb']
    exact toOrthogonal_coordinates b (e w)
  have hf (k : K) : f k = Binary.linearAction (κm k) := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [Binary.linearAction_apply,sourceStarAction_apply]
    exact hm k v
  have hquot : IsPGroup 2 ((F.H ⧸ pCore 2 F.H) ⧸ K) := by
    have hK : K = pResidual 2 (F.H ⧸ pCore 2 F.H) :=
      map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)
    exact (isPGroup_quotient_pResidual 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hK.symm)
  have hpow : (QuotientGroup.mk' (pCore 2 F.H) i)^2=1 := by
    rw [←map_pow]
    have hi2 : i^2=1 := Subtype.ext (hio ▸ pow_orderOf_eq_one (i:G))
    rw [hi2,map_one]
  have hs : Binary.InvolutionResidual.SwapsFactors
      (f (QuotientGroup.mk' (pCore 2 F.H) i)) :=
    source_orthogonal_selected_swaps_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he i hiX hiV
  have hr := diagonalResidual_image_of_comparison F.H z i hz hH.le
    (source_orthogonal_centralizer_comparison_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he z hzp hH i hiX hiV hio)
  rw [hr]
  exact Components.of_matrix_swap K κm hquot (pCore_quotient_pCore_eq_bot 2)
    f hf _ hpow hs

theorem source_selected_contradiction_of_moved_model_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (z x : G) (hz : orderOf z = 2) (hzp : F.Vi 1 = zpowers z)
    (hH : F.H = centralizer ({z} : Set G))
    (hiT : conjugateElement z x ∈ T) (hout : conjugateElement z x ∉ F.U)
    (hiX : conjugateElement z x ∈ F.X g)
    (hiV : conjugateElement z x ∉ centralizer (V : Set G))
    (hKU : diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
      normalizer (F.U : Set G))
    (m : MovedCoreModel F.U
      (diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x))
      (conjugateElement z x) hKU)
 : False := by
  have hio : orderOf (conjugateElement z x) = 2 := by
    simpa only [conjugateElement,MulEquiv.orderOf_eq] using hz
  have hc := fun hiH : conjugateElement z x ∈ F.H => source_orthogonal_selected_components_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he z hz hzp hH ⟨_,hiH⟩ hiX hiV hio
  rw [hH] at hc
  exact source_selected_contradiction_of_diagonal_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he z x hz hzp hH hiT hout hiX hiV hKU m (hc _).some

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

end

/- Specialization of CaseOneLarge/Orthogonal/MovedModule.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS


noncomputable section


noncomputable section


noncomputable section




namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative commutatorElement

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.Orthogonal CoreGeometry

open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

variable [IsMulCommutative V]
local instance (F : InvariantFlag T V 3) : (F.U.subgroupOf F.H).Normal := F.U_normal

theorem source_orthogonal_moved_model_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : let := chosen.elementary
      let := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v))
    (z : G) (hz : orderOf z = 2) (hzp : F.Vi 1 = zpowers z)
    (hH : F.H = centralizer ({z} : Set G))
    (i : F.H) (hiX : (i:G) ∈ F.X g)
    (hiV : (i:G) ∉ centralizer (V : Set G)) (hio : orderOf (i:G) = 2) :
    ∃ hKU : diagonalResidual F.H (i:G) ≤ normalizer (F.U : Set G),
      Nonempty (MovedCoreModel F.U (diagonalResidual F.H (i:G)) (i:G) hKU) := by
  let := chosen.elementary
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  let m := source_orthogonal_action_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he
  let K := diagonalResidual F.H (i:G)
  have hKH : K ≤ F.H := (map_subtype_le _).trans inf_le_left
  have hKi : K ≤ centralizer ({(i:G)} : Set G) := (map_subtype_le _).trans inf_le_right
  let B := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  let b : B ≃* Binary.G := κ.trans elementaryEquiv.symm
  let f := sourceStarAction F hk e
  have hf (h : F.H) : m.action h = f (QuotientGroup.mk' (pCore 2 F.H) h) := rfl
  have hb (k : B) : f k = Binary.linearAction (b k) := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := (e.trans Binary.binaryCoordinates).surjective w
    rw [sourceStarAction_apply,Binary.linearAction_apply]
    change Binary.binaryCoordinates (e ((sourceAction F hk).representation k v)) = _
    rw [he]
    obtain ⟨a,ha⟩ := elementaryEquiv.surjective (κ k)
    have ha' : b k = a := by
      change elementaryEquiv.symm (κ k) = a
      rw [←ha,elementaryEquiv.symm_apply_apply]
    rw [←ha,ha']
    exact toOrthogonal_coordinates a (e v)
  have hr := diagonalResidual_image_of_comparison F.H z i hz hH.le
    (source_orthogonal_centralizer_comparison_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he z hzp hH i hiX hiV hio)
  have hIB : (K.subgroupOf F.H).map (QuotientGroup.mk' (pCore 2 F.H)) ≤ B := by
    rw [hr]
    change _ ≤ (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
    rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
    exact map_pResidual_le 2 _
  let c := (source_orthogonal_selected_components_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he z hz hzp hH i hiX hiV hio).some
  refine ⟨hKH.trans m.normalizes,?_⟩
  exact movedCoreModel_of_star F.H F.U K m hKH
    (source_orthogonal_twoCore_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he).2 i hKi hio
    (source_orthogonal_action_swaps_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he i hiX hiV)
    (source_orthogonal_moved_rank_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he i hiX hiV hio).1 B b f hf hb hIB
    (selectedResidualEquiv c)

theorem source_orthogonal_contradiction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : let := chosen.elementary
      let := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) : False := by
  obtain ⟨hcore,z,hzo,hzp,hH,k,hk,hio,hiX,hiT,hiU,hiV⟩ :=
    source_orthogonal_selected_involution_at d earlier hq chosen structural alternatives
      F hne hZ g hg hgP hgH κ e he
  have hmoved := source_orthogonal_moved_model_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he z hzo hzp hH ⟨_,F.invariant 1 hiT⟩ hiX hiV hio
  change ∃ hKU : diagonalResidual F.H (conjugateElement z (g*k*g)) ≤ normalizer (F.U : Set G),
    Nonempty (MovedCoreModel F.U (diagonalResidual F.H (conjugateElement z (g*k*g)))
      (conjugateElement z (g*k*g)) hKU) at hmoved
  rw [hH] at hmoved
  obtain ⟨hKU,hm⟩ := hmoved
  exact source_selected_contradiction_of_moved_model_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he z (g*k*g) hzo hzp hH hiT hiU hiX hiV hKU hm.some

theorem source_orthogonal_exclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : let := chosen.elementary
      let := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) : False := by
  obtain ⟨g, hg, hgP, hgH⟩ := exists_source_conjugator_at d earlier hq chosen structural F
  exact source_orthogonal_contradiction_at d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH κ e he

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal

end

end

end

end

/- Specialization of CaseOneLarge/ComponentOrbitExclusion.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open ClassicalOrthogonal.FourPlusMatrix



open Subgroup Module Representation Theory.GroupTheory

open ClassicalOrthogonal.FourPlusMatrix


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

open ClassicalOrthogonal.FourPlusMatrix

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open LargerDimension LargerDimension.LocalAction.Components

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction.Components CoreGeometry

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

attribute [local instance 2000] instAlgebraZModGaloisField

theorem source_large_irreducible_orbit_binary_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C (componentOrbit C ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) :
    ∃ e : componentOrbit C ⊤ ≃* Binary.G,
      ∃ f : Additive F.Uhat ≃ₗ[ZMod 2] Binary.V,
        ∀ (a : componentOrbit C ⊤) w,
          f (F.terminalRepresentation a w) = Binary.action (e a) (f w) := by
  obtain ⟨n,hn,hmodel⟩ := source_large_irreducible_orbit_natural_at d earlier hq chosen
    structural alternatives classification F hne hZ hlarge g hgP hgH C hC hm h9
  obtain ⟨_,_,B,v,hyp,hline,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hfix : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v} ∨ ChapterG.Section11.LowRankWitness
        F.terminalRepresentation v (F.terminalDot (F.X g)) := by
    rcases source_terminal_fixed_point_alternative_at d earlier hq chosen structural alternatives
      F hne g hgP hgH v hline with hf | ⟨a,_,hr,hv⟩
    · exact .inl hf
    · exact .inr ⟨a,a.property,hr,hv⟩
  let := h9.normal_H
  have hn2 := OrthogonalOrbit.field_degree_eq_two hn hmodel v hyp.point_ne_zero hfix
  subst n
  obtain ⟨e,f,hf⟩ := hmodel
  refine ⟨e.trans Binary.galoisGroupEquiv,f.trans Binary.galoisCoordinates,?_⟩
  intro a w
  change Binary.galoisCoordinates (f (F.terminalRepresentation a w)) = _
  have hh := hf a w
  change f (F.terminalRepresentation a w) = _ at hh
  rw [hh]
  exact Binary.galoisCoordinates_intertwines (e a) (f w)

theorem source_large_irreducible_orbit_marked_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C (componentOrbit C ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) :
    ∃ κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃*
      ClassicalOrthogonal.OmegaPlus 2 Binary.F,
    ∃ e : Additive F.Uhat ≃ₗ[ZMod 2] ClassicalOrthogonal.VectorD 2 Binary.F,
      let := chosen.elementary
      let := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) w,
        e ((sourceAction F (source_terminal_kernel_at F d earlier hq chosen structural alternatives
          hne hZ)).representation k w) =
          ClassicalOrthogonal.subgroupNatural (ClassicalOrthogonal.OmegaPlus 2 Binary.F) (κ k) (e w) := by
  let := chosen.elementary
  let := F.U_normal
  let := h9.normal_H
  obtain ⟨e,f,hf⟩ := source_large_irreducible_orbit_binary_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH C hC hm h9
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hres := OrthogonalOrbit.residual_eq_of_coordinates F.terminalRepresentation
    hyp.faithful B hyp.nondegenerate hyp.preserves (componentOrbit C ⊤) e f hf
  let hk := source_terminal_kernel_at F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  let R := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  have hR : R.map q.toMonoidHom = componentOrbit C ⊤ := by
    dsimp only [R]
    rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),
      map_pResidual_of_surjective 2 _ q.surjective,hres]
  let eR : R ≃* componentOrbit C ⊤ :=
    (q.subgroupMap R).trans (MulEquiv.subgroupCongr hR)
  refine ⟨(eR.trans e).trans elementaryEquiv, f.trans Binary.binaryCoordinates.symm,?_⟩
  dsimp only
  intro k w
  apply Binary.binaryCoordinates.injective
  change Binary.binaryCoordinates (Binary.binaryCoordinates.symm
    (f (F.terminalRepresentation (q k.val) w))) = _
  rw [Binary.binaryCoordinates.apply_symm_apply]
  change f (F.terminalRepresentation (eR k) w) =
    Binary.binaryCoordinates (((elementaryEquiv (e (eR k))).val.val)
      (Binary.binaryCoordinates.symm (f w)))
  rw [hf]
  rw [show Binary.binaryCoordinates (((elementaryEquiv (e (eR k))).val.val)
      (Binary.binaryCoordinates.symm (f w))) =
      Binary.action (e (eR k)) (Binary.binaryCoordinates (Binary.binaryCoordinates.symm (f w))) from
        toOrthogonal_coordinates (e (eR k)) (Binary.binaryCoordinates.symm (f w))]
  rw [Binary.binaryCoordinates.apply_symm_apply]

theorem source_no_irreducible_component_orbit_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C (componentOrbit C ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) : False := by
  obtain ⟨κ,e,he⟩ := source_large_irreducible_orbit_marked_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH C hC hm h9
  let := chosen.elementary
  exact Orthogonal.source_orthogonal_exclusion_at d earlier hq chosen structural alternatives
    F hne hZ κ e he

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open LargerDimension LargerDimension.LocalAction.Components

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_large_point_constituent_isotropic_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C, F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I)
    (hv : v ∈ I) : ∀ u ∈ I, ∀ w ∈ I, B u w = 0 := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  rcases hyp.constituent_isotropic_or_top_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv with hiso | ⟨_,hirr⟩
  · exact hiso
  · exact (source_no_irreducible_component_orbit_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH C hC hm
      (hyp.componentHypothesis_of_orbit_irreducible (source_terminal_cover F d chosen)
        hC hm hind hirr)).elim

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_large_lowRank_exchanged_reduction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hfix : ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v)
    (hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
      (IsIrreducible F.terminalRepresentation ∧
        ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
          ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
          ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
            ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
              (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
              v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry
                F.terminalRepresentation B v (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
              (∃ x : F.terminalDot (F.X g), I.map (F.terminalRepresentation x) ≠ I ∧
                IsCompl I (I.map (F.terminalRepresentation x))) ∧
              finrank (ZMod 2) (Additive F.Uhat) = 2 * finrank (ZMod 2) I ∧
              (finrank (ZMod 2) (Additive F.Uhat) = 8 ∨
                finrank (ZMod 2) (Additive F.Uhat) = 12) ∧
              (B.restrict I).Nondegenerate ∧
              ∃ n, 5 ≤ n ∧ n ≤ 8 ∧ n ≠ 7 ∧ ChapterG.Section06.HasModelOn
                (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
                  (componentOrbit C ⊤) (F.terminalDot (F.X g) ⊓
                    subspaceStabilizer F.terminalRepresentation I) I hI.invariant inf_le_right)) ⊤ ⊤
                (BinaryPermutation.naturalRepresentation (Fin n))) := by
  rcases source_large_lowRank_reduction_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH B v hyp hfix hw with hc | ⟨hi,_,C,hC,hm,horth,hwhole | hex⟩
  · exact .inl hc
  · exact (source_no_irreducible_component_orbit_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH C hC hm hwhole).elim
  · exact .inr ⟨hi,C,hC,hm,horth,hex⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end
