module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterOrder
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedCoreStructure

/-!
# Exact original mixed orders in the commuting distance-one branch

The original A₅/S₃ markings provide the two turns needed by the exact
center-order theorem. Thus the beta center has order two, the alpha core
is elementary of order sixteen, and the beta core has order thirty-two.
The source intersection layer vanishes on every nonbacktracking alpha turn.
The existing literal reduced-to-original transport then gives order 64
for the full Borel two-core and order 64 or 128 for the original Sylow.

Only the original source hypotheses and the commuting distance-one branch
remain. The critical pair and both original quotient markings are retained.
These numerical and local statements do not identify the marked amalgam.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.6)(b,c), (11.7)(c,e), printed pp.172--175, and (15.1), p.226.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] [Finite G] (K U₀ S : Subgroup G)
local notation "F" => Reduction.reducedFamily ![K,U₀] S
local notation "M" => Reduction.G₀ ![K,U₀] S
local notation "α" => base F false
local notation "β" => base F true

private def mixed_alpha_marking (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3)) :
    (stabilizer F α ⧸ pCore 2 (stabilizer F α)) ≃* alternatingGroup (Fin 5) := by
  have he : Nonempty ((Reduction.P₀ ![K,U₀] S 0 ⧸ pCore 2 (Reduction.P₀ ![K,U₀] S 0)) ≃*
      alternatingGroup (Fin 5)) := by
    rw [Reduction.P₀_eq_source h 0]
    exact h.mixed_reduced_first_quotient eK eU
  let e₀ := subgroupOfEquivOfLe (show Reduction.P₀ ![K,U₀] S 0 ≤ M from le_sup_left)
  let eq₀ := QuotientGroup.congr _ _ e₀ (pCore_map_iso 2 e₀)
  have hs : stabilizer F α = (Reduction.P₀ ![K,U₀] S 0).subgroupOf M :=
    Subgroup.CosetGeometry.stabilizer_base _ _
  let es := MulEquiv.subgroupCongr hs
  let eqs := QuotientGroup.congr _ _ es (pCore_map_iso 2 es)
  exact (eqs.trans eq₀).trans he.some

private theorem mixed_turn (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) :
    ∃ c : Vertex F, (graph F).Adj β c ∧ α ≠ c ∧
      ∃ g : M, g ∈ stabilizer F α ∧ g • β ≠ β := by
  have hca := mixed_reduced_neighbor_cards K U₀ S h eK eU α
  have hcb := mixed_reduced_neighbor_cards K U₀ S h eK eU β
  obtain ⟨c,hbc,hca'⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet β)
    (by rw [←Nat.card_coe_set_eq,hcb]; change 1 < 3; decide) α
  obtain ⟨b',hab',hbb'⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet α)
    (by rw [←Nat.card_coe_set_eq,hca]; change 1 < 5; decide) β
  obtain ⟨g,hga,hgb⟩ := locally_transitive F (source_critical_one_adjacent hc hb) hab'
  exact ⟨c,hbc,Ne.symm hca',g,hga,by rw [hgb]; exact hbb'⟩

/-- The original mixed beta center has order two, without any layer-order premise. -/
theorem mixed_binary_graph_beta_center_card_two (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥) :
    Nat.card (Z F β) = 2 := by
  obtain ⟨c,hbc,hac,g,hga,hgb⟩ := mixed_turn K U₀ S h eK eU hc hb
  exact source_cubic_a5_center_card_two (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hc hb hcomm hbc hac (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
    (mixed_alpha_marking K U₀ S h eK eU) g hga hgb

/-- The source intersection layer vanishes at every nonbacktracking alpha turn. -/
theorem mixed_binary_graph_intersection_layer_eq_bot (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (b' d : Vertex F) (hab' : (graph F).Adj α b') (hbb' : β ≠ b')
    (hb'd : (graph F).Adj b' d) (had : α ≠ d) :
    neighborCoreIntersection F β ⊓ Q F b' = ⊥ := by
  have hI := (mixed_binary_graph_core_structure K U₀ S h eK eU hc hb hcomm).1
  have htwo := mixed_binary_graph_beta_center_card_two K U₀ S h eK eU hc hb hcomm
  have hnot := source_cubic_a5_layer_card_ne_two (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hc hb (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
    (mixed_alpha_marking K U₀ S h eK eU) hab' hbb' hb'd had
  have hd := card_dvd_of_le (inf_le_left :
    neighborCoreIntersection F β ⊓ Q F b' ≤ neighborCoreIntersection F β)
  have hIcard : Nat.card (neighborCoreIntersection F β) = 2 := by rw [hI,htwo]
  rw [hIcard] at hd
  exact eq_bot_of_card_eq _ ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right hnot)

/-- Exact local orders, including the corrected Chapter 11 span Vβ. -/
theorem mixed_binary_graph_exact_local_orders (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥) :
    Q F α = Z F α ∧ betaSpan (stabilizer F β) (Z F α) = Q F β ∧
      Nat.card (Z F α) = 16 ∧ Nat.card (Z F α ⊓ Q F β : Subgroup M) = 8 ∧
      Nat.card (Q F β) = 32 :=
  mixed_binary_graph_local_orders_of_beta_center_order K U₀ S h eK eU hc hb hcomm
    (mixed_binary_graph_beta_center_card_two K U₀ S h eK eU hc hb hcomm)

/-- DGS (11.7)(c) in the literal original mixed-size consumer: the full Borel
core has order 64, and its extension to the original Sylow has order at most 128. -/
theorem mixed_binary_graph_exact_row_size (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥) :
    Nat.card (twoCore (commonBorel ![K,U₀] S)) = 64 ∧
      (Nat.card S = 64 ∨ Nat.card S = 128) :=
  mixed_binary_graph_row_size_of_beta_center_order K U₀ S h eK eU hc hb hcomm
    (mixed_binary_graph_beta_center_card_two K U₀ S h eK eU hc hb hcomm)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
