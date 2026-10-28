module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedSplitting
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Source

/-!
# The span-core intersections on the extended critical path

The reciprocal field index and the cubic span order identify the terminal
span's intersection with the beta core as the middle natural center. At
the other end, the original trivial displacement identifies the forward
span-core intersection; the direct sum of central neighboring lines then
makes the preceding line disjoint from the terminal core.

These are the literal geometric inputs to the fixed-point and direct-product
steps of DGS 9.10(4), printed p.148.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The reciprocal index identifies the terminal span-core intersection
on the same path; its cubic order is transported from the beta span. -/
theorem graph_terminal_span_core_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta x a' : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta) (hbx : (graph (family P)).Adj beta x)
    (hxa' : (graph (family P)).Adj x a') (hb : 1 < b (family P))
    {q : ℕ} (hq : 0 < q)
    (ha : Nat.card (Z (family P) a) = q^2)
    (hV : Nat.card (V (family P) beta 1) = q^3)
    (hi : (Q (family P) beta).relIndex (V (family P) a' 1) = q) :
    V (family P) a' 1 ⊓ Q (family P) beta = Z (family P) x := by
  let := finite_endpoints h
  let Γ := family P
  obtain ⟨g,hg,hgd⟩ := graphLocalGroup_transitive h hB hS x ⟨beta,hbx.symm⟩ ⟨a',hxa'⟩
  change g • beta = a' at hgd
  have hVd : Nat.card (V Γ a' 1) = q^3 := by
    rw [←hgd,V_translate,card_map_of_injective (MulAut.conj g).injective]
    exact hV
  obtain ⟨k,hk,hkx⟩ := graphLocalGroup_transitive h hB hS beta ⟨a,hab.symm⟩ ⟨x,hbx⟩
  change k • a = x at hkx
  have hZx : Nat.card (Z Γ x) = q^2 := by
    rw [←hkx,Z_translate,card_map_of_injective (MulAut.conj k).injective]
    exact ha
  have hZI : Z Γ x ≤ V Γ a' 1 ⊓ Q Γ beta := le_inf
    (CommutingNontrivial.Z_neighbor_le_V Γ hxa'.symm)
    (Z_le_Q_of_dist_lt_b Γ (fun v => (source_Z_Q_U h v).1) (source_kernel_sylow h hB hS)
      x beta (by rwa [SimpleGraph.dist_eq_one_iff_adj.mpr hbx.symm]))
  let : Finite (V Γ a' 1 ⊓ Q Γ beta : Subgroup G) := Finite.of_injective
    (inclusion (inf_le_right.trans (Q_le_stabilizer Γ beta))) (inclusion_injective _)
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (V Γ a' 1 ⊓ Q Γ beta) (V Γ a' 1)
    bot_le inf_le_left
  simp only [relIndex_bot_left,inf_relIndex_left] at hc
  rw [hi,hVd] at hc
  have he : Nat.card (V Γ a' 1 ⊓ Q Γ beta : Subgroup G) = q^2 :=
    Nat.eq_of_mul_eq_mul_right hq (hc.trans (pow_succ q 2))
  exact (eq_of_le_of_card_ge hZI (by rw [he,hZx])).symm

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The source trivial-displacement identity and the two direct central
lines force the preceding line to avoid the terminal core. -/
theorem reduced_preceding_line_disjoint_terminal_core
    (h : HypothesisF11 L S)
    {a beta x a' l : Vertex (Reduction.reducedFamily L S)}
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 = b (Reduction.reducedFamily L S))
    (htriv : ⁅V (Reduction.reducedFamily L S) beta 1 ⊓ Q (Reduction.reducedFamily L S) a',
      V (Reduction.reducedFamily L S) a' 1⁆ = ⊥)
    (hcentral : V (Reduction.reducedFamily L S) beta 1 ⊓
      centralizer (V (Reduction.reducedFamily L S) a' 1 : Set (Reduction.G₀ L S)) =
      Z (Reduction.reducedFamily L S) x)
    (hspan : Z (Reduction.reducedFamily L S) a = Z (Reduction.reducedFamily L S) beta ⊔
      Z (Reduction.reducedFamily L S) l)
    (hAV : Z (Reduction.reducedFamily L S) a ≤ V (Reduction.reducedFamily L S) beta 1)
    (hcut : Z (Reduction.reducedFamily L S) a ⊓ Z (Reduction.reducedFamily L S) x =
      Z (Reduction.reducedFamily L S) beta)
    (hdis : Disjoint (Z (Reduction.reducedFamily L S) beta) (Z (Reduction.reducedFamily L S) l)) :
    Disjoint (Z (Reduction.reducedFamily L S) l) (Q (Reduction.reducedFamily L S) a') := by
  let Γ := Reduction.reducedFamily L S
  have hVQ : V Γ beta 1 ⊓ Q Γ a' = Z Γ x :=
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv).symm.trans hcentral
  have hlA : Z Γ l ≤ Z Γ a := le_sup_right.trans hspan.ge
  apply disjoint_def.mpr
  intro z hzl hzQ
  apply disjoint_def.mp hdis ?_ hzl
  rw [←hcut]
  exact ⟨hlA hzl,hVQ ▸ (show z ∈ V Γ beta 1 ⊓ Q Γ a' from ⟨hAV (hlA hzl),hzQ⟩)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
