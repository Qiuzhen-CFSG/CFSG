module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NeighborSeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CubicIntersections

/-!
# Original mixed-pair applications of the neighboring-core separation

The original A₅/S₃ quotient markings give the literal reduced alpha
quotient and cubic beta valence. Thus every turn of the reduced graph
satisfies the separation and elementary Z₀ conclusions proved in
`NeighborSeparation`. The full local kernels and their actual Sylow
cores remain distinct throughout the transport.

The later numerical consumer takes the two still-unproved structural
assertions Qα = Zα and Z₀ = 1. The cubic action then proves the neighboring
intersection has order two; transporting Qα = Zα to the other alpha vertex
identifies it with the seed intersection. The established count gives
|O₂(B)| = 64 and the original |S| = 64 or 128. This does not discharge the
two structural assertions or establish the complete (11.7) profile.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.5)--(11.7), printed pp.172--175, and reduction (15.1), printed p.226.
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

private def mixed_alpha_quotient (h : HypothesisF11 ![K,U₀] S)
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

/-- The source separation step on every original mixed-pair turn. -/
theorem mixed_binary_graph_neighbor_intersection_separated (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (b' d : Vertex F) (hab' : (graph F).Adj α b') (hbb' : β ≠ b')
    (hb'd : (graph F).Adj b' d) (had : α ≠ d) :
    neighborCoreIntersection F β ⊓ Q F d = ⊥ :=
  source_cubic_a5_neighbor_intersection_separated_at_turn (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hc hb
    (mixed_reduced_neighbor_cards K U₀ S h eK eU β) (mixed_alpha_quotient K U₀ S h eK eU)
    hab' hbb' hb'd had

/-- The literal subgroup Z₀ of (11.6) is elementary of order at most four.
All local quotient and kernel hypotheses are supplied by the original mixed pair. -/
theorem mixed_binary_graph_intersection_layer (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (b' d : Vertex F) (hab' : (graph F).Adj α b') (hbb' : β ≠ b')
    (hb'd : (graph F).Adj b' d) (had : α ≠ d) :
    IsElementaryAbelian 2 (neighborCoreIntersection F β ⊓ Q F b' : Subgroup M) ∧
      Nat.card (neighborCoreIntersection F β ⊓ Q F b' : Subgroup M) ≤ 4 :=
  source_cubic_a5_intersection_layer (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hc hb
    (mixed_reduced_neighbor_cards K U₀ S h eK eU β) (mixed_alpha_quotient K U₀ S h eK eU)
    hab' hbb' hb'd had

/-- Vanishing of the source layer Z₀ gives order two for the full neighboring-core
intersection, using its actual action at the other cubic vertex. -/
theorem mixed_binary_graph_neighbor_intersection_card_of_layer (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (b' : Vertex F) (hab' : (graph F).Adj α b')
    (hzero : neighborCoreIntersection F β ⊓ Q F b' = ⊥) :
    Nat.card (neighborCoreIntersection F β) = 2 := by
  let I := neighborCoreIntersection F β
  have ht := Reduction.reduced_triple h
  have hab := source_critical_one_adjacent hc hb
  have hIa : I ≤ Q F α := neighborCoreIntersection_le _ hab
  have hp : IsPGroup 2 I := (isPGroup_pCoreIn 2 _).to_le hIa
  have hIb' : I ≤ stabilizer F b' := hIa.trans ((source_Z_Q_U ht α).2.trans
    ((ballKernel_one_le_edge _ hab').trans inf_le_right))
  have hne : I ≠ ⊥ := by
    intro he
    apply base_Z_ne_bot ht true
    exact bot_unique ((reduced_commuting_one_center_le_neighbor_intersection h hc hb hcomm).trans he.le)
  have hesc : ¬ I ≤ U F b' := by
    intro hh
    have hIQ := CommutingTrivial.two_subgroup_le_Q F b' (Reduction.reduced_kernel_sylow h b') hp hh
    apply hne
    calc
      I = I ⊓ Q F b' := (inf_eq_left.mpr hIQ).symm
      _ = ⊥ := hzero
  obtain ⟨g,_,hgb⟩ := locally_transitive F hab hab'
  have hb't : b'.type = true := (congrArg (fun v : Vertex F => v.type) hgb).symm
  have hcard : Nat.card ((graph F).neighborSet b') = 3 := by
    rw [mixed_reduced_neighbor_cards K U₀ S h eK eU b',hb't]
    rfl
  have hi := source_cubic_two_subgroup_index ht b' I hp hIb' hesc hcard
    (Reduction.reduced_kernel_sylow h b')
  change (I ⊓ Q F b').relIndex I = 2 at hi
  have hzero' : I ⊓ Q F b' = ⊥ := hzero
  rw [hzero',relIndex_bot_left] at hi
  exact hi

/-- Once Qα = Zα and the remaining Z₀ vanishing are established, the actual
seed intersection has order two. No seed order is taken as a premise. -/
theorem mixed_binary_graph_seed_intersection_card_of_layer (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (c b' : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c)
    (hab' : (graph F).Adj α b')
    (hQa : Q F α = Z F α) (hzero : neighborCoreIntersection F β ⊓ Q F b' = ⊥) :
    Nat.card ((Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) : Subgroup M) = 2 := by
  have ht := Reduction.reduced_triple h
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨g,_,hgc⟩ := locally_transitive F hab.symm hbc
  have hQc : Q F c = Z F c := by
    rw [←hgc,Q_translate,Z_translate,hQa]
  have he : (Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) = Z F α ⊓ Z F c :=
    source_cubic_seed_intersection_eq_center_intersection ht hc hb hbc hac
      (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
  have hi : Q F α ⊓ Q F c = neighborCoreIntersection F β :=
    source_cubic_core_pair_eq_neighbor_intersection ht hc hb hbc hac
      (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
  rw [he,←hQa,←hQc,hi]
  exact mixed_binary_graph_neighbor_intersection_card_of_layer K U₀ S h eK eU hc hb hcomm b' hab' hzero

/-- Literal original-Sylow size consumer, now with only the two remaining
structural source assertions Qα = Zα and Z₀ = 1 explicit. -/
theorem mixed_binary_graph_row_size_of_layer (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (c b' : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c)
    (hab' : (graph F).Adj α b')
    (hQa : Q F α = Z F α) (hzero : neighborCoreIntersection F β ⊓ Q F b' = ⊥) :
    Nat.card (twoCore (commonBorel ![K,U₀] S)) = 64 ∧
      (Nat.card S = 64 ∨ Nat.card S = 128) :=
  mixed_binary_graph_row_size_of_intersection K U₀ S h eK eU hc hb c hbc hac hQa
    (mixed_binary_graph_seed_intersection_card_of_layer K U₀ S h eK eU hc hb hcomm
      c b' hbc hac hab' hQa hzero)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
