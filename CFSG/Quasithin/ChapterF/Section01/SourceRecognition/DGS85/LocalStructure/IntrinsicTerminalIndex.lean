module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicRadiusAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalSection

/-!
# Intrinsic terminal actors and their subgroup indices

The actual radius quotient constructed in `IntrinsicRadiusAction` applies to
any subgroup of the abelian radius-two span that reaches the last odd vertex.
Its second commutator vanishes by the existing radius calculation, and its
image under the literal core quotient has order equal to the ambient relative
core index. Fixed quotient coordinates then compare this index with the
centralizer index on the radius-one span. A sharp index recognizes the actual
terminal quotient, including exclusion of a possible order-144 enlargement.

This supplies the module estimate used in the final radius-intersection
argument without a global actor catalogue. The geometric upper bound and
terminal selection remain separate source obligations.
Source: DGS, *Groups and Graphs* (1985), (7.5), pp.130--131,
with the fixed-space-generation correction to (5.12).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Noncommuting
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- The literal terminal actor index and its sharp linear recognition criterion. -/
theorem reduced_long_terminal_actor_index (h : HypothesisF11 L S)
    {v w t y : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : 4 < b F) (hwt : (graph F).Adj w t)
    (hdt : (graph F).dist v t + 1 = b F) (hty : (graph F).Adj t y)
    (hcore : V F v 2 ≤ Q F y)
    (A : Subgroup (G₀ L S)) (hAV : A ≤ V F v 2) (hesc : ¬ A ≤ Q F t) :
    (Q F t).relIndex A ≤ (centralizer (A : Set (G₀ L S))).relIndex (V F t 1) ∧
      ((centralizer (A : Set (G₀ L S))).relIndex (V F t 1) ≤ (Q F t).relIndex A →
        ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
          (graphLocalGroup F t ⧸ pCore 2 (graphLocalGroup F t)) 2 (2^n)) := by
  let ht := reduced_triple h
  let := finite_endpoints ht
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let M := graphLocalGroup F t
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : ((Q F t).subgroupOf M).Normal := by
    rw [graph_intrinsic_core ht t]
    infer_instance
  have hrev := (reduced_noncommuting_critical_intersections h hc hne).1
  obtain ⟨W,hadd,hmodule,σ,s,_hnt,hfin,hcompare⟩ :=
    reduced_long_critical_radius_comparison h hrev (by rwa [commutator_comm])
      (by omega) hwt (by rwa [SimpleGraph.dist_comm])
  let := hadd
  let := hmodule
  let := hfin
  let π := QuotientGroup.mk' ((Q F t).subgroupOf M)
  have hp : IsPGroup 2 A :=
    (graph_V_isPGroup_of_short ht (reduced_kernel_sylow h) v (by omega : 2 < b F)).to_le hAV
  have hAP : A ≤ stabilizer F t :=
    ((hAV.trans hcore).trans (source_Z_Q_U ht y).2).trans
      ((ballKernel_one_le_edge F hty.symm).trans inf_le_right)
  have hAM : A ≤ M := pGroup_le_sylowGenerated _ _ hAP hp
  let : Finite A := Finite.of_injective (inclusion hAM) (inclusion_injective _)
  let : Finite (V F t 1) := Finite.of_injective
    (inclusion s.section_le) (inclusion_injective _)
  let Abar := (A.subgroupOf M).map π
  obtain ⟨T,hAT⟩ := hp.comap_subtype.exists_le_sylow (G := M)
  have hbar : Abar ≤ (T : Subgroup M).map π := map_mono hAT
  have hcard : Nat.card Abar = (Q F t).relIndex A :=
    actor_image_card_eq_relIndex M (Q F t) A π (QuotientGroup.ker_mk' _) hAM
  have hgt : 1 < Nat.card Abar := by
    rw [hcard]
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨index_ne_zero_of_finite,fun he => hesc (relIndex_eq_one.mp he)⟩
  have hquad : IsQuadratic σ Abar := by
    apply isQuadratic_of_triple_commutator_le M (V F t 1) (Z F t) A σ π s
    exact ((commutator_mono hAV (commutator_mono hAV le_rfl)).trans
      (graph_radius_two_triple_commutator ht (reduced_kernel_sylow h) hdt hb).le).trans bot_le
  have hlower := hcompare T Abar hbar hgt hquad
  have hupper : Nat.card (W ⧸ fixedSpace σ Abar) ≤
      (centralizer (A : Set (G₀ L S))).relIndex (V F t 1) :=
    fixed_quotient_card_le_centralizer_index σ π s A
  refine ⟨hcard ▸ hlower.1.trans hupper,?_⟩
  intro hsharp
  obtain ⟨n,hn,hm⟩ := hlower.2 (hupper.trans (hsharp.trans_eq hcard.symm))
  exact ⟨n,hn,hm.of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (graph_intrinsic_core ht t)).symm⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
