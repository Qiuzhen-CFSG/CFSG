module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterPoint
public import CFSG.Quasithin.Chapter12.Section08.Terminal
public import CFSG.Quasithin.ChapterG.Section10.NumericalGeometry

/-!
# Original 14.3.12 on the selected nonabelian rank-two closure

The displaced-center kernel is the conjugate marked point. Consequently
the smaller dotted actor is the actual center modulo that point. The G.10
numerical equality forces this actor to vanish in the small-rank branch,
and hence forces Z(U)=V₁. Its exact rank and intersection dimension then
supply the extraspecial and maximal-singular square-form conclusions.

The final source application constructs the original flag, conjugator,
dotted action and SQTK cover from the selected rank-two prefix. In the
complementary center branch it gives the bound d≤2m, without a recognition
or geometry callback.

Source: Aschbacher--Smith, 12.8.10--13 and 14.3.12, printed pp.853--855,993.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {V : Subgroup G} {L M : Subgroup G}

theorem rankTwo_terminal_center_kernel (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype =
      conjugate (F.Vi 1) g := by
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨_,_,_,_,hIG,hIN,_⟩ := F.binary_generation (by decide) L h.L_normalizes_seed
    (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare hspan hne g hgP hgH
  let B := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
  have hc := F.binary_source_center_calculations (by decide) L h.L_normalizes_seed
    ((pResidual_eq_top_iff 2 L).mp h.L_residual) h.sylow_normalizes_L
    (h.binarySeedAction_surjective F) (fun hn => by omega) h.centralizer d.seed_center
    hcomm hsquare hspan hne g hgP hgH d.tilde_kernel B
  have hdis := (F.parabolic_displaced_centers (by decide) L h.L_normalizes_seed
    d.seed_center g hgP hgH).1
  have hzero := (F.rankTwo_centers L g (F.P_le_seed_normalizer L h.L_normalizes_seed hgP)
    (h.sylowOmega_eq_point F) (F.binary_U_le_sylow (by decide) hsquare)
    ((F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN))
    d.seed_center hdis hc.2.1).1
  have hk := hc.2.2.2.2.2
  change conjugate F.ZU g ⊓ F.uhatAction.ker.map F.H.subtype = _
  calc
    _ = Chapter12.Section08.centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g :=
      hk.1.trans (hk.2.1.trans (hk.2.2.1.trans (hk.2.2.2.1.trans hk.2.2.2.2.1)))
    _ = _ := by rw [hzero,bot_sup_eq]

/-- The source smaller actor is the actual center modulo the marked point. -/
noncomputable def rankTwo_terminal_center_equiv (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (F.ZU ⧸ (F.Vi 1).subgroupOf F.ZU) ≃* F.terminalDot (conjugate F.ZU g) :=
  F.terminalCenterQuotientEquiv g
    (F.conjugate_center_le_H g (F.P_le_seed_normalizer L h.L_normalizes_seed hgP))
    (rankTwo_terminal_center_kernel h F d hne g hgP hgH)

theorem rankTwo_center_eq_point_of_smaller_bot (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hbot : (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)) = ⊥) :
    F.ZU = F.Vi 1 := by
  have hle : F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  have hd : F.terminalDot (conjugate F.ZU g) = ⊥ := by
    have hh := congrArg (fun A : Subgroup (F.terminalDot (F.X g)) =>
      A.map (F.terminalDot (F.X g)).subtype) hbot
    simpa only [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using hh
  apply le_antisymm _ (F.point_le_ZU (by decide))
  intro z hz
  let hn := F.conjugate_center_le_H g (F.P_le_seed_normalizer L h.L_normalizes_seed hgP)
  have hm : F.terminalCenterImageMap g hn ⟨z,hz⟩ = 1 := by
    apply Subtype.ext
    have hh := (F.terminalCenterImageMap g hn ⟨z,hz⟩).property
    exact (show F.terminalDot (conjugate F.ZU g) ≤ (⊥ : Subgroup F.TerminalHdot) from hd.le) hh
  have hk := F.terminalCenterImageMap_ker g hn
    (rankTwo_terminal_center_kernel h F d hne g hgP hgH)
  have hh : (⟨z,hz⟩ : F.ZU) ∈ (F.terminalCenterImageMap g hn).ker := hm
  rw [hk] at hh
  exact hh

/-- The complement of the small-actor branch has degree at most twice its rank. -/
theorem rankTwo_dimension_le_twice_actor_of_center_ne_point
    (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hZ : F.ZU ≠ F.Vi 1) :
    Module.finrank (ZMod 2) (Additive F.Uhat) ≤
      2 * Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  apply hyp.dimension_le_twice_actor_of_smaller_ne_bot
  intro hb
  exact hZ (rankTwo_center_eq_point_of_smaller_bot h F d hne g hgP hgH hb)

/-- The literal numerical and center conclusions of original 14.3.12(1--3). -/
theorem rankTwo_small_actor_geometry (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hm : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1) :
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) = ⊥ ∧
    Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) =
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1 ∧
    Module.finrank (ZMod 2) (hatSpace F (F.E g)) =
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 ∧
    F.ZU = F.Vi 1 ∧ F.terminalHatAction.ker = pCore 2 F.H := by
  obtain ⟨hb,hm,he⟩ := hyp.numerical_equality_of_actor_dimension_le hm
  have hz := rankTwo_center_eq_point_of_smaller_bot h F d hne g hgP hgH hb
  exact ⟨hb,hm,he,hz,terminal_kernel_of_center_point F d hz⟩

/-- The complete numerical and quadratic conclusions of original 14.3.12,
with its actual flag, conjugator, dotted actor and square form. -/
structure SmallActorConclusions (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))] : Prop where
  smaller_bot : ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) = ⊥
  actor_rank : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) =
    Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1
  intersection_dimension : Module.finrank (ZMod 2) (hatSpace F (F.E g)) =
    Module.finrank (ZMod 2) (Additive F.Uhat) / 2
  center_point : F.ZU = F.Vi 1
  extraspecial : IsExtraspecial 2 F.U
  tilde_to_hat : Function.Bijective (F.tildeToUhat (by decide))
  dotted_kernel : F.terminalHatAction.ker = pCore 2 F.H
  singular : ∀ x ∈ hatSpace F (F.E g), centerPointQuadraticForm F d (by decide) center_point x = 0
  invariant : ∀ (h : F.H) (x : F.Uhat),
    centerPointQuadraticForm F d (by decide) center_point (Additive.ofMul (F.uhatAction h x)) =
      centerPointQuadraticForm F d (by decide) center_point (Additive.ofMul x)
  nondegenerate : (centerPointQuadraticForm F d (by decide) center_point).polarBilin.Nondegenerate
  maximal_singular : ∀ S : Submodule (ZMod 2) (Additive F.Uhat), hatSpace F (F.E g) ≤ S →
    (∀ x ∈ S, centerPointQuadraticForm F d (by decide) center_point x = 0) → S = hatSpace F (F.E g)

theorem rankTwo_small_actor_conclusions (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hm : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1) :
    SmallActorConclusions F d g := by
  obtain ⟨hb,hr,he,hZ,hk⟩ := rankTwo_small_actor_geometry h F g d hne hgP hgH hyp hm
  have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU := disjoint_iff.mpr
    (F.parabolic_displaced_centers (by decide) L h.L_normalizes_seed
      d.seed_center g hgP hgH).1
  obtain ⟨hs,hi,hnd⟩ := quadratic_intersection_of_center_point F d (by decide) hZ g hdis
  exact ⟨hb,hr,he,hZ,extraspecial_of_center_point F d (by decide) hZ hne,
    tildeToUhat_bijective_of_center_point F (by decide) hZ,hk,hs,hi,hnd,
    maximal_singular_of_half_dimension F d (by decide) hZ g hdis he⟩

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
/-- Original 14.3.12 from the selected rank-two prefix. The source itself
supplies every flag, conjugator, quotient action and preceding geometry input. -/
theorem source_lemma_14_3_12
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ∃ hs : IsElementaryAbelian 2 (rankTwoSeed T M), letI := hs
    ∃ F : InvariantFlag T (rankTwoSeed T M) 2,
      F.Vi 1 = centralInvolutions T ∧ F.H = Mc ∧
      F.U = conjugateSpanBy (localModule T M) Mc ∧
    ∃ d : ClosureGeometry F, ∃ he : IsElementaryAbelian 2 F.Uhat, letI := he
    ∃ g : G, g ∈ F.P (sourceResidual M Mc) ∧ g ∉ F.H ∧
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat), ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot) ∧
      (Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
        Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1 → SmallActorConclusions F d g) ∧
      (F.ZU ≠ F.Vi 1 → Module.finrank (ZMod 2) (Additive F.Uhat) ≤
        2 * Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by
  obtain ⟨hs,F,hpoint,hH,hU,d,he,g,hgP,hgH,hx,B,v,hyp,hcover⟩ :=
    source_terminal_hypothesis hG T hempty hM hu hmany hcard e hne
  let := hs
  let := he
  let := hx
  have hn : ¬ IsMulCommutative F.U := hU ▸ hne
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  exact ⟨hs,F,hpoint,hH,hU,d,he,g,hgP,hgH,hx,B,v,hyp,hcover,
    rankTwo_small_actor_conclusions h F d hn g hgP hgH hyp,
    rankTwo_dimension_le_twice_actor_of_center_ne_point h F g d hn hgP hgH hyp⟩


end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
