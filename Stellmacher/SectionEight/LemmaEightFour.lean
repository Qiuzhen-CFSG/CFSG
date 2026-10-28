module

public import Stellmacher.QuotientModuleOffenderFixedPoints
public import Stellmacher.SectionFiveToSeven.Result7_4
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionEight.EightFourSourceNineCoreGeneration
public import Stellmacher.SectionEight.EightFourSourceNineTerminalInvariantReduction

/-!
# The barred fixed-center normality assertion in Stellmacher (8.4)

For a noncommuting critical pair whose first-step center is central in its
stabilizer, the fixed subgroup of Section One's J on the faithful initial-center
quotient is normal in the first-step stabilizer. The explicit quotient-module
witness retains the original action. Its fixed subgroup is independent of the
faithful presentation; it is the barred expression in the printed source.

The opening reduction puts the fixed subgroup in the first-step core and reduces
normality to equality with its normal closure. In the contrary branch, the proved
source-(4) closure control and the actual quotient/involution configurations from
(7.8), together with (8.3) and the (6.4) centralizer criterion, construct the
transported edge-fixed family and source-(9) data. The length-two contradiction
forces critical length greater than two. The subsequent commutator and index
arguments show that the fixed subgroup has order four and the first-step core
acts nontrivially on its full closure.

The final core-generation lemma uses the faithful fixed-space fixer and the
order-four action to show that the two adjacent cores generate the distinguished
Sylow. The terminal invariant-subgroup theorem then puts the selected transported
fixed subgroup inside the original endpoint center, contradicting its proved
noncontainment. This closes the nontrivial-closure branch without assuming that
an adjacent stabilizer normalizes the initial center. Only the proved (7.8)
configuration leaves are used, not its unfinished uniform Baumann assertion.

The local theorem retains the actual graph and quotient witness and takes
only the two proved ambient inputs packaged by EightFourLocalContext. The
canonical theorem is an exact wrapper; generated contexts use the same proof
through their own ambient-backed adapter.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.4), printed pp.38–40,
`refs/files/stellmacher-n-group.pdf`. The opening S1 is the normal closure of the
opposite endpoint center. The former raw LocalJ expression had a different
offender denominator and is not identified with this barred fixed subgroup.
-/

namespace Stellmacher.SectionEight

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven
open CosetGraphContext

universe u

private theorem normalClosure_core_reduction
    {H : Type u} [Group H] (F P : Subgroup H)
    (hFcore : F ≤ twoCoreIn P) :
    let C := (Subgroup.normalClosure (F.subgroupOf P : Set P)).map P.subtype
    F ≤ C ∧ C ≤ twoCoreIn P ∧ (NormalIn F P ↔ C = F) := by
  let C := (Subgroup.normalClosure (F.subgroupOf P : Set P)).map P.subtype
  have hFP : F ≤ P := hFcore.trans (Subgroup.map_subtype_le _)
  have hFC : F ≤ C := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hFP]
    exact Subgroup.map_mono Subgroup.le_normalClosure
  have hsub : F.subgroupOf P ≤ pCore 2 P := by
    intro element helement
    obtain ⟨preimage, hpreimage, heq⟩ := hFcore helement
    have hsame : preimage = element := Subtype.ext heq
    exact hsame ▸ hpreimage
  have hCcore : C ≤ twoCoreIn P :=
    Subgroup.map_mono (Subgroup.normalClosure_le_normal hsub)
  refine ⟨hFC, hCcore, ?_⟩
  constructor
  · intro hnormal
    let _ := hnormal.2
    change (Subgroup.normalClosure (F.subgroupOf P : Set P)).map P.subtype = F
    rw [Subgroup.normalClosure_eq_self, Subgroup.map_subgroupOf_eq_of_le hFP]
  · intro heq
    refine ⟨hFP, ?_⟩
    rw [← heq]
    change ((Subgroup.normalClosure (F.subgroupOf P : Set P)).map P.subtype
      |>.comap P.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
    infer_instance

private theorem fixed_center_le_next_core
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hlen : 1 < ctx.criticalPath.length)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    w.oneJFixedPoints S ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  have hfixed : w.oneJFixedPoints S ≤ ZAt ctx.Γ ctx.criticalPath.a :=
    Subgroup.map_subtype_le _
  apply hfixed.trans
  apply SevenSix.critical_minimality ctx.Γ ctx.criticalPath
  have hdist := (SevenSix.adjacent_iff_distance_eq_one ctx.Γ).mp
    ctx.criticalPath.firstStep_adj
  rw [hdist]
  exact hlen

/-- Fixed-center normality from the same local graph and its proved ambient inputs. -/
public theorem lemma_eight_four_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : EightFourLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    NormalIn (w.oneJFixedPoints S)
      (GAt ctx.Γ ctx.criticalPath.firstStep) := by
  have hlen : 1 < ctx.criticalPath.length := eight_four_centered_length_gt_one_local ctx.toLocalContext hcenter
  have hfixed : w.oneJFixedPoints S ≤ QAt ctx.Γ ctx.criticalPath.firstStep :=
    fixed_center_le_next_core ctx.toLocalContext hlen w
  have hcore : QAt ctx.Γ ctx.criticalPath.firstStep =
      twoCoreIn (GAt ctx.Γ ctx.criticalPath.firstStep) := by
    exact ctx.Γ.twoCoreAt_def ctx.criticalPath.firstStep
  rw [hcore] at hfixed
  apply (normalClosure_core_reduction (w.oneJFixedPoints S)
    (GAt ctx.Γ ctx.criticalPath.firstStep) hfixed).2.2.mpr
  by_cases hclosure :
      (Subgroup.normalClosure
        ((w.oneJFixedPoints S).subgroupOf
          (GAt ctx.Γ ctx.criticalPath.firstStep) : Set
          (GAt ctx.Γ ctx.criticalPath.firstStep))).map
        (GAt ctx.Γ ctx.criticalPath.firstStep).subtype =
      w.oneJFixedPoints S
  · exact hclosure
  · obtain ⟨F, hbase, hcov, hsub, hformula⟩ :=
      eight_four_edge_fixed_transport_local ctx.toLocalContext hcenter w hclosure
    obtain ⟨configuration⟩ := eight_four_source_nine_configuration_local
      ctx hcenter w hclosure F hbase hcov hsub hformula
    have hlong : 2 < ctx.criticalPath.length := by
      have hne := eight_four_length_ne_two_of_nontrivial_closure_local ctx hcenter w hclosure
      omega
    have hgeneration := eight_four_source_nine_core_generation_local
      ctx.toLocalContext hcenter w hclosure F hbase hcov hsub hformula configuration hlong
    have hterminal := eight_four_source_nine_terminal_invariant_of_core_generation_local
      ctx.toLocalContext hcenter w hclosure F hbase hcov hsub hformula configuration hlong hgeneration
    exact (eight_four_source_nine_fixed_not_le_terminal_local
      ctx.toLocalContext hcenter w hclosure F hbase hcov hsub configuration
        (hterminal.trans inf_le_left)).elim

/-- **Stellmacher (8.4).**  The subgroup
`Z=C_{Z_a}(J(Z_a,\bar S))` is normal in `G_{a+1}` when the first-step center
is central. The explicit faithful witness presents the barred action. -/
public theorem lemma_eight_four
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    NormalIn (w.oneJFixedPoints S)
      (GAt ctx.Γ ctx.criticalPath.firstStep)  := by
  exact lemma_eight_four_local ctx.toEightFourContext hcenter w

end Stellmacher.SectionEight
