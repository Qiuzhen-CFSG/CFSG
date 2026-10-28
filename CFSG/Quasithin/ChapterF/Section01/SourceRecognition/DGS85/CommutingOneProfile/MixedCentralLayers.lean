module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CardinalControl
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedSeparation

/-!
# The original mixed Chapter 11 count from the remaining center layer

The original A₅/S₃ markings yield the center and mixed core-center
intersection identities on the same reduced graph. They identify the
source Z₀ with Zβ intersect Qβ′ and prove its centralization of Qα.

If this remaining center layer vanishes, cubic index two gives Iβ = Zβ
of order two. The cardinal comparisons then prove Qα = Zα, and the
established seed generation gives Qβ = Vβ with orders 16, 8 and 32 for
the alpha center, its seed and beta core. Thus the actual reduced Borel
radical has order 64 and the original Sylow has order 64 or 128. The
alpha-core equality is no longer an extra numerical-consumer premise.

Vanishing of the center layer still needs the source argument. These
conditional local consequences do not assert the full (11.7)--(11.8)
profiles, their path stabilizers, or a marked unitary-amalgam recognition.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.6)--(11.7), printed pp.172--175; reduction (15.1), printed p.226.
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

/-- The literal mixed core-center and seed intersections all equal Zβ. -/
theorem mixed_binary_graph_center_intersections (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (c : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c) :
    Z F α ⊓ Q F c = Z F β ∧ Q F α ⊓ Z F c = Z F β ∧
      Z F α ⊓ Z F c = Z F β ∧
      (Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) = Z F β := by
  have ht := Reduction.reduced_triple h
  have hcard := mixed_reduced_neighbor_cards K U₀ S h eK eU β
  have he := source_cubic_a5_center_intersection ht (Reduction.reduced_borel_core_sylow h)
    (Reduction.reduced_vertex_sylow h) hc hb hcomm hbc hac hcard
    (mixed_alpha_marking K U₀ S h eK eU)
  exact ⟨(source_cubic_center_inf_core ht hc hb hbc hac hcard).trans he,
    (source_cubic_core_inf_center ht hc hb hbc hac hcard).trans he,he,
    (source_cubic_seed_intersection_eq_center_intersection ht hc hb hbc hac hcard).trans he⟩

/-- The full source layer equals the beta-center layer, with the original graph retained. -/
theorem mixed_binary_graph_layer_eq_center_layer (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (c b' : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c)
    (hab' : (graph F).Adj α b') (hbb' : β ≠ b') :
    neighborCoreIntersection F β ⊓ Q F b' = Z F β ⊓ Q F b' := by
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨g,hga,hgb⟩ := locally_transitive F hab hab'
  have he := source_cubic_a5_layer_le_center (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hc hb hbc hac (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
    (mixed_alpha_marking K U₀ S h eK eU) g hga (by change g • β ≠ β; rw [hgb]; exact Ne.symm hbb')
  change neighborCoreIntersection F β ⊓ Q F (g • β) ≤ Z F β at he
  rw [hgb] at he
  exact le_antisymm (le_inf he inf_le_right)
    (inf_le_inf_right _ (reduced_commuting_one_center_le_neighbor_intersection h hc hb hcomm))

/-- The source layer centralizes the original reduced alpha core. -/
theorem mixed_binary_graph_layer_centralizes_core (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (c b' : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c)
    (hab' : (graph F).Adj α b') (hbb' : β ≠ b') :
    neighborCoreIntersection F β ⊓ Q F b' ≤ centralizer (Q F α : Set M) := by
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨g,hga,hgb⟩ := locally_transitive F hab hab'
  have he := source_cubic_a5_layer_centralizes_core (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hc hb hbc hac (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
    (mixed_alpha_marking K U₀ S h eK eU) g hga (by change g • β ≠ β; rw [hgb]; exact Ne.symm hbb')
  change neighborCoreIntersection F β ⊓ Q F (g • β) ≤ centralizer (Q F α : Set M) at he
  rwa [hgb] at he

/-- The original-Sylow count from the alpha-core equality and beta-center order. -/
theorem mixed_binary_graph_row_size_of_center_order (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (c : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c)
    (hQa : Q F α = Z F α) (hZb : Nat.card (Z F β) = 2) :
    Nat.card (twoCore (commonBorel ![K,U₀] S)) = 64 ∧
      (Nat.card S = 64 ∨ Nat.card S = 128) := by
  apply mixed_binary_graph_row_size_of_intersection K U₀ S h eK eU hc hb c hbc hac hQa
  rw [(mixed_binary_graph_center_intersections K U₀ S h eK eU hc hb hcomm c hbc hac).2.2.2]
  exact hZb


/-- Vanishing of the center layer gives Iβ = Zβ, its order two, and Qα = Zα. -/
theorem mixed_binary_graph_core_center_of_center_layer (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (c b' : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c)
    (hab' : (graph F).Adj α b') (hbb' : β ≠ b')
    (hzero : Z F β ⊓ Q F b' = ⊥) :
    neighborCoreIntersection F β = Z F β ∧ Nat.card (Z F β) = 2 ∧ Q F α = Z F α := by
  have hzero' : neighborCoreIntersection F β ⊓ Q F b' = ⊥ := by
    rw [mixed_binary_graph_layer_eq_center_layer K U₀ S h eK eU hc hb hcomm c b'
      hbc hac hab' hbb',hzero]
  have hI := mixed_binary_graph_neighbor_intersection_card_of_layer K U₀ S h eK eU hc hb hcomm
    b' hab' hzero'
  have hZI := reduced_commuting_one_center_le_neighbor_intersection h hc hb hcomm
  have hZne : Nat.card (Z F β) ≠ 1 := fun hh =>
    base_Z_ne_bot (Reduction.reduced_triple h) true (card_eq_one.mp hh)
  have hZpos : 0 < Nat.card (Z F β) := Nat.card_pos
  have he : neighborCoreIntersection F β = Z F β :=
    (eq_of_le_of_card_ge hZI (by omega)).symm
  have hZcard : Nat.card (Z F β) = 2 := by rw [←he];exact hI
  refine ⟨he,hZcard,?_⟩
  exact source_cubic_a5_core_eq_center_of_intersection (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hc hb hcomm hbc hac (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
    (mixed_alpha_marking K U₀ S h eK eU) he

/-- The actual corrected Vβ equals Qβ, with the source core and seed orders. -/
theorem mixed_binary_graph_local_orders_of_center_layer (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (c b' : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c)
    (hab' : (graph F).Adj α b') (hbb' : β ≠ b')
    (hzero : Z F β ⊓ Q F b' = ⊥) :
    Q F α = Z F α ∧ betaSpan (stabilizer F β) (Z F α) = Q F β ∧
      Nat.card (Z F α) = 16 ∧ Nat.card (Z F α ⊓ Q F β : Subgroup M) = 8 ∧
      Nat.card (Q F β) = 32 := by
  obtain ⟨_,hZb,hQa⟩ := mixed_binary_graph_core_center_of_center_layer K U₀ S h eK eU
    hc hb hcomm c b' hbc hac hab' hbb' hzero
  have hinter : Nat.card ((Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) : Subgroup M) = 2 := by
    rw [(mixed_binary_graph_center_intersections K U₀ S h eK eU hc hb hcomm c hbc hac).2.2.2]
    exact hZb
  have hgen := mixed_binary_graph_core_generation K U₀ S h eK eU hc hb c hbc hac
  have hpair := beta_core_eq_pairSpan_of_alpha_core_eq _ _ _ _ hgen hQa
  exact ⟨hQa,source_betaSpan_eq_core_of_pairSpan (Reduction.reduced_triple h)
    (source_critical_one_adjacent hc hb) hbc hpair.symm,
    mixed_binary_graph_seed_orders_of_intersection K U₀ S h eK eU hc hb c hbc hac hQa hinter⟩

/-- The original mixed numerical consumer with only the remaining center-layer vanishing explicit. -/
theorem mixed_binary_graph_row_size_of_center_layer (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (c b' : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c)
    (hab' : (graph F).Adj α b') (hbb' : β ≠ b')
    (hzero : Z F β ⊓ Q F b' = ⊥) :
    Nat.card (twoCore (commonBorel ![K,U₀] S)) = 64 ∧
      (Nat.card S = 64 ∨ Nat.card S = 128) := by
  obtain ⟨_,hZb,hQa⟩ := mixed_binary_graph_core_center_of_center_layer K U₀ S h eK eU
    hc hb hcomm c b' hbc hac hab' hbb' hzero
  exact mixed_binary_graph_row_size_of_center_order K U₀ S h eK eU hc hb hcomm c hbc hac hQa hZb

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
