module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CubicGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterIdentities
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedCubicApplication

/-!
# Pairwise neighboring-core intersections at a cubic vertex

Each of two neighboring centers centralizes the intersection of their
cores. If the center pair is transitive on the beta star, conjugating one
core by that pair places the intersection in every neighboring core.
Consequently the pairwise intersection equals the full neighboring-core
intersection and is normal in the full beta stabilizer. Critical escape
supplies the required transitivity at a cubic vertex.

The seed intersection is therefore the intersection of the two whole
centers. Together with (11.1), the actual beta center lies in that
intersection. These statements apply to the literal reduced mixed A5/S3
pair, without assuming core generation, center orders or a unitary
recognition. The reverse inclusion in (11.6)(a) remains a separate source
argument.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.6), printed pp.172--173, and the normality observation in the proof of
(11.7), printed p.174.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem center_pair_centralizes_core_pair (h : LocallyRankOneTriple P B)
    (a c : Vertex (family P)) :
    Z (family P) a ⊔ Z (family P) c ≤
      centralizer (Q (family P) a ⊓ Q (family P) c : Set G) := by
  apply sup_le
  · exact (le_centralizer_iff.mp (source_core_centralizes_center h a)).trans
      (centralizer_le inf_le_left)
  · exact (le_centralizer_iff.mp (source_core_centralizes_center h c)).trans
      (centralizer_le inf_le_right)

/-- Center-pair transitivity identifies the pairwise core intersection. -/
theorem source_core_pair_eq_neighbor_intersection_of_center_pair_transitive
    (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (ht : ∀ w, (graph (family P)).Adj b w →
      ∃ g ∈ Z (family P) a ⊔ Z (family P) c, g • a = w) :
    Q (family P) a ⊓ Q (family P) c = neighborCoreIntersection (family P) b := by
  apply le_antisymm
  · intro x hx
    apply mem_iInf.mpr
    intro w
    obtain ⟨g,hg,hga⟩ := ht w.val w.property
    have hgx := (mem_centralizer_iff.mp (center_pair_centralizes_core_pair h a c hg)) x hx
    have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom hx.1
    rw [←Q_translate,hga] at hm
    change g * x * g⁻¹ ∈ Q (family P) w.val at hm
    simpa only [←hgx,mul_inv_cancel_right] using hm
  · exact le_inf (neighborCoreIntersection_le _ hab) (neighborCoreIntersection_le _ hbc.symm)

/-- The pairwise neighboring-core identity on the cubic critical branch. -/
theorem source_cubic_core_pair_eq_neighbor_intersection (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3) :
    Q (family P) a ⊓ Q (family P) c = neighborCoreIntersection (family P) b :=
  source_core_pair_eq_neighbor_intersection_of_center_pair_transitive h
    (source_critical_one_adjacent hc hb) hbc
    (source_cubic_center_pair_transitive h hc hb hbc hac hcard)

/-- The source pairwise core intersection is normal in the full beta stabilizer. -/
theorem source_cubic_core_pair_normalized (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3) :
    stabilizer (family P) b ≤ normalizer
      ((Q (family P) a ⊓ Q (family P) c : Subgroup G) : Set G) := by
  rw [source_cubic_core_pair_eq_neighbor_intersection h hc hb hbc hac hcard]
  exact neighborCoreIntersection_normalized _ b

/-- Intersecting the two seeds is the same as intersecting their whole centers. -/
theorem source_cubic_seed_intersection_eq_center_intersection (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3) :
    (Z (family P) a ⊓ Q (family P) b) ⊓ (Z (family P) c ⊓ Q (family P) b) =
      Z (family P) a ⊓ Z (family P) c := by
  have hzq (v : Vertex (family P)) : Z (family P) v ≤ Q (family P) v :=
    (source_Z_Q_U h v).1.trans (map_subtype_le _)
  have hle : Z (family P) a ⊓ Z (family P) c ≤ Q (family P) b :=
    (inf_le_inf (hzq a) (hzq c)).trans
      ((source_cubic_core_pair_eq_neighbor_intersection h hc hb hbc hac hcard).le.trans
        (source_neighborCoreIntersection_le_core h (source_critical_one_adjacent hc hb)))
  exact le_antisymm
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
    (le_inf (le_inf inf_le_left hle) (le_inf inf_le_right hle))

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The pairwise core identity on the literal reduced F1.11 graph. -/
theorem reduced_cubic_core_pair_eq_neighbor_intersection (h : HypothesisF11 L S)
    {a b c : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a b)
    (hb : DGS85.b (Reduction.reducedFamily L S) = 1)
    (hbc : (graph (Reduction.reducedFamily L S)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (Reduction.reducedFamily L S)).neighborSet b) = 3) :
    Q (Reduction.reducedFamily L S) a ⊓ Q (Reduction.reducedFamily L S) c =
      neighborCoreIntersection (Reduction.reducedFamily L S) b :=
  source_cubic_core_pair_eq_neighbor_intersection (Reduction.reduced_triple h)
    hc hb hbc hac hcard

variable [Finite G] (K U₀ S : Subgroup G)
local notation "F" => Reduction.reducedFamily ![K,U₀] S
local notation "M" => Reduction.G₀ ![K,U₀] S
local notation "α" => base F false
local notation "β" => base F true

/-- The original mixed markings supply the cubic valence in the core identity. -/
theorem mixed_binary_graph_core_pair_intersection (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (c : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c) :
    Q F α ⊓ Q F c = neighborCoreIntersection F β ∧
      stabilizer F β ≤ normalizer ((Q F α ⊓ Q F c : Subgroup M) : Set M) := by
  have ht := Reduction.reduced_triple h
  have hcard := mixed_reduced_neighbor_cards K U₀ S h eK eU β
  exact ⟨source_cubic_core_pair_eq_neighbor_intersection ht hc hb hbc hac hcard,
    source_cubic_core_pair_normalized ht hc hb hbc hac hcard⟩

/-- The literal mixed seed intersection contains Zβ and equals Zα ∩ Zγ.
No order for that intersection is assumed or asserted here. -/
theorem mixed_binary_graph_seed_intersection (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (c : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c) :
    (Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) = Z F α ⊓ Z F c ∧
      Z F β ≤ (Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) := by
  have ht := Reduction.reduced_triple h
  have he := source_cubic_seed_intersection_eq_center_intersection ht hc hb hbc hac
    (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
  refine ⟨he,he ▸ ?_⟩
  exact le_inf
    (source_commuting_one_center_le_neighbor ht (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) hc hb hcomm (source_critical_one_adjacent hc hb).symm)
    (source_commuting_one_center_le_neighbor ht (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) hc hb hcomm hbc)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
