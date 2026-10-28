module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.MixedCentralizers

/-!
# The mixed quotient actors in the second case of DGS 9.3

When V_alpha_prime lies in Q_beta, the original critical center and that
opposite span normalize each other. Their literal conjugation actions
have exactly the opposite core intersections as kernels. Critical escape
makes both images nontrivial. The two centralizer indices therefore give
a strict square comparison in one direction, before natural recognition.

The reduced source application discharges the common Sylow, full-kernel
Sylow and central-vertex premises and retains both quadratic commutators.
Faithfulness of the full local quotient and Sylow-fixed generation on the
residual section remain necessary for corrected 5.12.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
9.3, second case, printed p.142.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The original critical center acts on the opposite neighboring span. -/
def mixedCenterAction (h : LocallyRankOneTriple P B)
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 ≤ b (family P)) :
    Z (family P) a →* MulAut (V (family P) a' 1) := by
  let := finite_endpoints h
  exact (V (family P) a' 1).normalizerMonoidHom.comp (inclusion
    (((CommutingNontrivial.Z_neighbor_le_V (family P) hab.symm).trans
      (V_le_stabilizer (family P) h.generate beta a' hd)).trans
        (stabilizer_normalizes_V (family P) a' 1)))

/-- The opposite span acts on the same critical center in the small-neighbor case. -/
def mixedNeighborAction (h : LocallyRankOneTriple P B)
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hs : V (family P) a' 1 ≤ Q (family P) beta) :
    V (family P) a' 1 →* MulAut (Z (family P) a) := by
  let := finite_endpoints h
  exact (Z (family P) a).normalizerMonoidHom.comp (inclusion
    ((hs.trans ((source_Z_Q_U h beta).2.trans
      ((ballKernel_one_le_edge (family P) hab.symm).trans inf_le_right))).trans
        (CommutingNontrivial.stabilizer_normalizes_Z (family P) a)))

theorem mixedCenterAction_apply (h : LocallyRankOneTriple P B)
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 ≤ b (family P))
    (x : Z (family P) a) (z : V (family P) a' 1) :
    (mixedCenterAction h hab hd x z : G) = (x : G) * z * (x : G)⁻¹ := rfl

theorem mixedNeighborAction_apply (h : LocallyRankOneTriple P B)
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hs : V (family P) a' 1 ≤ Q (family P) beta)
    (x : V (family P) a' 1) (z : Z (family P) a) :
    (mixedNeighborAction h hab hs x z : G) = (x : G) * z * (x : G)⁻¹ := rfl

/-- The center action has the literal opposite-core intersection as kernel. -/
theorem mixedCenterAction_ker (h : LocallyRankOneTriple P B)
    (hSyl : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 ≤ b (family P))
    (htriv : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ = ⊥) :
    (mixedCenterAction h hab hd).ker = (Q (family P) a').subgroupOf (Z (family P) a) := by
  have he := congrArg (fun A : Subgroup G => A.subgroupOf (Z (family P) a))
    (mixed_center_centralizer h hSyl hab hd htriv)
  simp only [inf_subgroupOf_left] at he
  rw [← he]
  unfold mixedCenterAction
  rw [← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

/-- The reciprocal action has the starting-core intersection as kernel. -/
theorem mixedNeighborAction_ker (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hz : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta))
    (hs : V (family P) a' 1 ≤ Q (family P) beta) :
    (mixedNeighborAction h hab hs).ker = (Q (family P) a).subgroupOf (V (family P) a' 1) := by
  have he := congrArg (fun A : Subgroup G => A.subgroupOf (V (family P) a' 1))
    (mixed_neighbor_centralizer h hB hS hab hz hs)
  simp only [inf_subgroupOf_left] at he
  rw [← he]
  unfold mixedNeighborAction
  rw [← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

/-- Both original quotient actors are nontrivial; their orders are the exact
core indices appearing in the second case of 9.3. -/
theorem mixed_action_orders (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hSyl : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 ≤ b (family P))
    (hz : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta))
    (htriv : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ = ⊥)
    (hs : V (family P) a' 1 ≤ Q (family P) beta) :
    Nat.card (mixedCenterAction h hab hd).range = (Q (family P) a').relIndex (Z (family P) a) ∧
      Nat.card (mixedNeighborAction h hab hs).range = (Q (family P) a).relIndex (V (family P) a' 1) ∧
      1 < Nat.card (mixedCenterAction h hab hd).range ∧
      1 < Nat.card (mixedNeighborAction h hab hs).range := by
  let := finite_endpoints h
  let : Finite (Z (family P) a) := Finite.of_injective
    (inclusion (Z_le_stabilizer (family P) a)) (inclusion_injective _)
  let : Finite (V (family P) a' 1) := Finite.of_injective
    (inclusion (hs.trans (Q_le_stabilizer (family P) beta))) (inclusion_injective _)
  have he₀ : Nat.card (mixedCenterAction h hab hd).range =
      (Q (family P) a').relIndex (Z (family P) a) := by
    rw [← index_ker, mixedCenterAction_ker h hSyl hab hd htriv]
    rfl
  have he₁ : Nat.card (mixedNeighborAction h hab hs).range =
      (Q (family P) a).relIndex (V (family P) a' 1) := by
    rw [← index_ker, mixedNeighborAction_ker h hB hS hab hz hs]
    rfl
  refine ⟨he₀, he₁, ?_, ?_⟩
  · rw [he₀]
    apply one_lt_index_of_ne_top
    intro he
    exact hc.2 ((subgroupOf_eq_top.mp he).trans (source_Z_Q_U h a').2)
  · rw [he₁]
    apply one_lt_index_of_ne_top
    exact fun he => mixed_neighbor_escape h hSyl hc hab hd htriv (subgroupOf_eq_top.mp he)

/-- The mixed reciprocal indices force one strict square comparison before
any natural-module recognition. -/
theorem mixed_strict_comparison (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hSyl : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 ≤ b (family P))
    (hz : Z (family P) beta = omegaCenterIn (graphLocalGroup (family P) beta))
    (htriv : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ = ⊥)
    (hs : V (family P) a' 1 ≤ Q (family P) beta) :
    (centralizer (V (family P) a' 1 : Set G)).relIndex (Z (family P) a) <
        Nat.card (mixedNeighborAction h hab hs).range ^ 2 ∨
      (centralizer (Z (family P) a : Set G)).relIndex (V (family P) a' 1) <
        Nat.card (mixedCenterAction h hab hd).range ^ 2 := by
  obtain ⟨he₀, he₁, h₀, h₁⟩ := mixed_action_orders h hB hS hSyl hc hab hd hz htriv hs
  have hc₀ := congrArg (fun C : Subgroup G => C.relIndex (Z (family P) a))
    (mixed_center_centralizer h hSyl hab hd htriv)
  have hc₁ := congrArg (fun C : Subgroup G => C.relIndex (V (family P) a' 1))
    (mixed_neighbor_centralizer h hB hS hab hz hs)
  simp only [inf_relIndex_left] at hc₀ hc₁
  rw [hc₀, hc₁, ← he₀, ← he₁]
  rcases le_total (Nat.card (mixedCenterAction h hab hd).range)
      (Nat.card (mixedNeighborAction h hab hs).range) with hle | hle
  · left; nlinarith
  · right; nlinarith

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal small-neighbor branch has both nontrivial quotient actors,
exact kernels and indices, mutual quadratic commutators, and a strict
comparison in at least one direction. Every local Sylow premise is discharged. -/
theorem reduced_critical_mixed_actions (h : HypothesisF11 L S)
    {a beta a' : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (hab : (graph (Reduction.reducedFamily L S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 = b (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hcomm : ⁅Z (Reduction.reducedFamily L S) a, Z (Reduction.reducedFamily L S) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S) beta 1 ⊓ Q (Reduction.reducedFamily L S) a',
      V (Reduction.reducedFamily L S) a' 1⁆ = ⊥)
    (hs : V (Reduction.reducedFamily L S) a' 1 ≤ Q (Reduction.reducedFamily L S) beta) :
    let F := Reduction.reducedFamily L S
    let f := mixedCenterAction (Reduction.reduced_triple h) hab hd.le
    let g := mixedNeighborAction (Reduction.reduced_triple h) hab hs
    f.ker = (Q F a').subgroupOf (Z F a) ∧
      g.ker = (Q F a).subgroupOf (V F a' 1) ∧
      Nat.card f.range = (Q F a').relIndex (Z F a) ∧
      Nat.card g.range = (Q F a).relIndex (V F a' 1) ∧
      1 < Nat.card f.range ∧ 1 < Nat.card g.range ∧
      ⁅⁅Z F a, V F a' 1⁆, Z F a⁆ = ⊥ ∧
      ⁅⁅Z F a, V F a' 1⁆, V F a' 1⁆ = ⊥ ∧
      ((centralizer (V F a' 1 : Set (Reduction.G₀ L S))).relIndex (Z F a) <
          Nat.card g.range ^ 2 ∨
        (centralizer (Z F a : Set (Reduction.G₀ L S))).relIndex (V F a' 1) <
          Nat.card f.range ^ 2) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S
  let : ∀ i, Finite (F i) := finite_endpoints ht
  obtain ⟨_, _, hz, hquad, _⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  obtain ⟨he₀, he₁, hn₀, hn₁⟩ := mixed_action_orders ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    (Reduction.reduced_kernel_sylow h) hc hab hd.le hz htriv hs
  have hZV : Z F a ≤ V F beta 1 := CommutingNontrivial.Z_neighbor_le_V F hab.symm
  refine ⟨mixedCenterAction_ker ht (Reduction.reduced_kernel_sylow h) hab hd.le htriv,
    mixedNeighborAction_ker ht (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) hab hz hs,
    he₀, he₁, hn₀, hn₁, ?_, ?_, ?_⟩
  · exact bot_unique ((commutator_mono (commutator_mono hZV le_rfl) hZV).trans_eq hquad.1)
  · exact bot_unique ((commutator_mono (commutator_mono hZV le_rfl) le_rfl).trans_eq hquad.2)
  · exact mixed_strict_comparison ht (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) (Reduction.reduced_kernel_sylow h)
      hc hab hd.le hz htriv hs

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
