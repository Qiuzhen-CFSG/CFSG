module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SeedEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NeighborIntersection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Neighborhood
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.OuterTransport
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound

/-!
# Original mixed-pair applications of the Chapter 11 seed geometry

The reduced F1.11 graph supplies the normal Sylow of each full local kernel
and the two-closed full reduced Borel. Thus its Chapter 11 neighboring-core
centralizer is transitive, and the degree-three seed escapes the full
opposite kernel U, not just Q.

For the original A5/S3 markings, the exact reduced Borel indices give
valences five and three. The cubic seed theorem therefore applies to the
same graph, centers, cores and inclusions without additional local-action
premises. This removes the seed-escape step from the mixed source branch;
the generation, cardinalities and complete (11.7) profile needed for its
Sylow bound remain to be established by this owner.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.2)(c), p.168; opening of (11.6), p.172; (6.2)(b,d), p.119, and the
original/reduced-pair transport in (15.1), p.226.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The first centralizer-transitivity step of (11.6) on the literal
reduced graph, with two-closedness discharged from original F1.11. -/
theorem reduced_neighbor_core_centralizer_transitive (h : HypothesisF11 L S)
    {a b c : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a b)
    (hb : DGS85.b (Reduction.reducedFamily L S) = 1)
    (hbc : (graph (Reduction.reducedFamily L S)).Adj b c) :
    ∃ g ∈ stabilizer (Reduction.reducedFamily L S) b ⊓ centralizer
      (neighborCoreIntersection (Reduction.reducedFamily L S) b : Set (Reduction.G₀ L S)),
      g • a = c :=
  source_neighbor_core_centralizer_transitive (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) hc hb hbc

/-- On the reduced cubic branch the seed escapes the full opposite kernel,
using the actual normal Sylow of Uγ supplied by (6.2)(d). -/
theorem reduced_cubic_seed_escapes_full_kernel (h : HypothesisF11 L S)
    {a b c : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a b)
    (hb : DGS85.b (Reduction.reducedFamily L S) = 1)
    (hbc : (graph (Reduction.reducedFamily L S)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (Reduction.reducedFamily L S)).neighborSet b) = 3) :
    ¬ Z (Reduction.reducedFamily L S) a ⊓ Q (Reduction.reducedFamily L S) b ≤
      U (Reduction.reducedFamily L S) c := by
  have ht := Reduction.reduced_triple h
  let : ∀ i, Finite (Reduction.reducedFamily L S i) := finite_endpoints ht
  let : IsElementaryAbelian 2 (Z (Reduction.reducedFamily L S) a) :=
    source_center_elementary ht a
  let : IsElementaryAbelian 2 (Z (Reduction.reducedFamily L S) a ⊓
      Q (Reduction.reducedFamily L S) b : Subgroup (Reduction.G₀ L S)) :=
    IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
  intro he
  exact source_cubic_seed_escape ht hc hb hbc hac hcard
    (CommutingTrivial.two_subgroup_le_Q (Reduction.reducedFamily L S) c
      (Reduction.reduced_kernel_sylow h c) (IsElementaryAbelian.isPGroup 2
        (Z (Reduction.reducedFamily L S) a ⊓ Q (Reduction.reducedFamily L S) b :
          Subgroup (Reduction.G₀ L S))) he)

variable [Finite G] (K U₀ S : Subgroup G)
local notation "F" => Reduction.reducedFamily ![K,U₀] S
local notation "M" => Reduction.G₀ ![K,U₀] S
local notation "α" => base F false
local notation "β" => base F true

/-- Both valences of the actual reduced mixed graph, from the original
quotient markings. The full reduced overlap is retained. -/
theorem mixed_reduced_neighbor_cards (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (v : Vertex F) :
    Nat.card ((graph F).neighborSet v) = if v.type then 3 else 5 := by
  have ht := Reduction.reduced_triple h
  apply card_neighbors_of_indices F (fun i => if i then 3 else 5)
  intro i
  cases i
  · change (F true).relIndex (F false) = 5
    rw [←inf_relIndex_right (F true) (F false),inf_comm,
      show F false ⊓ F true = (Reduction.B₀ ![K,U₀] S).subgroupOf M from ht.intersection]
    change ((Reduction.B₀ ![K,U₀] S).subgroupOf M).relIndex
      ((Reduction.P₀ ![K,U₀] S 0).subgroupOf M) = 5
    rw [relIndex_subgroupOf (show Reduction.P₀ ![K,U₀] S 0 ≤ M from le_sup_left),
      Reduction.B₀_eq_source h,Reduction.P₀_eq_source h]
    exact ((SuzukiContainment.reduced_hypothesis h).mixed_borel_parabolic_indices eK eU).1
  · change (F false).relIndex (F true) = 3
    rw [←inf_relIndex_right (F false) (F true),
      show F false ⊓ F true = (Reduction.B₀ ![K,U₀] S).subgroupOf M from ht.intersection]
    change ((Reduction.B₀ ![K,U₀] S).subgroupOf M).relIndex
      ((Reduction.P₀ ![K,U₀] S 1).subgroupOf M) = 3
    rw [relIndex_subgroupOf (show Reduction.P₀ ![K,U₀] S 1 ≤ M from le_sup_right),
      Reduction.B₀_eq_source h,Reduction.P₀_eq_source h]
    exact ((SuzukiContainment.reduced_hypothesis h).mixed_borel_parabolic_indices eK eU).2

/-- The literal mixed-pair seed has the escape and movement used in Chapter11;
no degree, non-two-group, kernel-Sylow, or elementary-center premise remains. -/
theorem mixed_binary_graph_seed_escape (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (c : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c) :
    ¬ IsPGroup 2 (Z F α ⊔ Z F c : Subgroup M) ∧
      (¬ Z F α ⊓ Q F β ≤ U F c) ∧
      ⁅Z F α ⊓ Q F β,Z F c⁆ ≠ ⊥ := by
  have ht := Reduction.reduced_triple h
  have hcard : Nat.card ((graph F).neighborSet β) = 3 :=
    mixed_reduced_neighbor_cards K U₀ S h eK eU β
  exact ⟨source_cubic_centers_not_isPGroup ht hc hb hbc hac hcard,
    reduced_cubic_seed_escapes_full_kernel h hc hb hbc hac hcard,
    source_cubic_seed_moved ht hc hb hbc hac hcard⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
