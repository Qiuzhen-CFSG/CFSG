module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5KernelAction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5Preparation
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixLargeRadicalGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActor

/-!
# Kernel comparison for the original normalized terminal A₅ component

The numerical alternatives of 14.3.14 suffice for the intrinsic kernel
comparison on the supplied component. The small-actor case uses 14.3.12;
degree four uses the displaced-center order bound and perfect action on
that small center; degree six with actor rank three uses the proved
ambient kernel equality. Every branch retains the original component.

The source application constructs its original G.10 geometry and connects
the resulting radical equality to the minimal-parabolic consumer. The
larger-actor numerical alternatives remain explicit: this module does not
assert their source proof or the unconditional A₅ exclusion of 14.3.15.

Source: Aschbacher--Smith, 12.8.13, 14.3.12--15 and G.11.2(2),(9),
printed pp.855--856,993--994 and 364--367.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}
    {T : Sylow 2 G} {L M : Subgroup G}

/-- Transport the restricted kernel equality through the literal inclusion
of the supplied component into the point normalizer. -/
theorem ComponentLift.radical_eq_twoCore_of_restricted_terminal_kernel
    {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hsmall : SmallImageRow F K)
    (hk : F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
      pCore 2 (K.subgroupOf F.H)) : solvableRadical K = pCore 2 K := by
  have hr := hK.terminal_kernel_eq_radical hsmall
  rw [ker_subgroupMap,QuotientGroup.ker_mk'] at hr
  change F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype = _ at hr
  rw [hk] at hr
  let e := subgroupOfEquivOfLe hK.le_pointNormalizer
  have he := congrArg (Subgroup.map e.toMonoidHom) hr
  rw [pCore_map_iso,map_solvableRadical_equiv] at he
  exact he.symm

/-- Each original numerical branch gives the intrinsic equality for the
same small-image component; no component rechoice is used. -/
theorem ComponentLift.radical_eq_twoCore_of_terminal_degrees
    (h : RankTwoHypothesis κ T L M)
    {F : InvariantFlag T (rankTwoSeed T M) 2}
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) {g : G}
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K) (hsmall : SmallImageRow F K)
    (hdegrees :
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
        finrank (ZMod 2) (Additive F.Uhat) / 2 - 1) ∨
      finrank (ZMod 2) (Additive F.Uhat) = 4 ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3)) :
    solvableRadical K = pCore 2 K := by
  let d := Recognition.rankTwo_closure_geometry h F hne
  rcases hdegrees with hm | hd | ⟨hd,hm⟩
  · apply hK.radical_eq_twoCore_of_restricted_terminal_kernel hsmall
    rw [(Recognition.rankTwo_small_actor_geometry h F g d hne hgP hgH hyp hm).2.2.2.2]
    exact (pCore_subnormal_eq_comap 2 hK.component.subnormal).symm
  · apply hK.radical_eq_twoCore_of_tilde_center_card_le_four hsmall d
    exact Recognition.rankTwo_tilde_center_card_le_four_of_dimension_four
      h F d hne g hgP hgH hyp hd
  · exact hK.radical_eq_twoCore_of_restricted_terminal_kernel hsmall
      (hK.restricted_kernel_of_six_three h hne hgP hgH hyp hd hm)

section Source
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hdegrees : ¬ (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1) →
      finrank (ZMod 2) (Additive F.Uhat) = 4 ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3))
include hG hempty hM hu hmany hcard e F hne g hgP hgH hK e5 hdegrees

set_option linter.unusedSectionVars false in
/-- The original geometry removes every kernel and action premise. Only
the independently produced larger-actor numerical alternatives remain. -/
theorem source_terminal_single_a5_radical_of_large_actor_degrees :
    solvableRadical K = pCore 2 K := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨hx,B,v,hyp,_⟩ :=
    source_component_lift_geometry hG T hempty hM hu hmany hcard e F hne g hgP hgH K hK
  have hyp' : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) := hyp
  apply hK.radical_eq_twoCore_of_terminal_degrees h hne hgP hgH hyp' (Or.inl ⟨e5⟩)
  by_cases hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1
  · exact Or.inl hm
  · exact Or.inr (hdegrees hm)

/-- Actual application to the original minimal-parabolic consumer, with
its radical premise discharged by the numerical-branch kernel proof. -/
theorem source_terminal_single_a5_parabolic_of_large_actor_degrees
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (hspan : K = conjugateSpanBy K (T : Subgroup G)) :
    let H := K ⊔ (T : Subgroup G)
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧
      H ∈ Chapter3.HStar (T : Subgroup G) M ∧
      (pResidual 2 H).map H.subtype = K ∧ (K.subgroupOf H).Normal ∧
      ChapterB.IsMinimalParabolicOver T H ∧ generalizedFitting H = pCore 2 H ∧
      (normalizer ((T : Subgroup G).subgroupOf K : Set K)).map K.subtype ≤ M := by
  exact source_terminal_single_a5_parabolic_of_radical hG T hempty hM hu hmany hcard e hnot
    hK hspan e5 (source_terminal_single_a5_radical_of_large_actor_degrees
      hG T hempty hM hu hmany hcard e F hne g hgP hgH hK e5 hdegrees)
end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
