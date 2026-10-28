module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CoreEquality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedCentralLayers

/-!
# Original mixed core structure without a vanishing assumption

The original A₅/S₃ quotient markings and the actual reduced graph supply
the turns and local quotient needed by `CoreEquality`. This gives
Iβ = Zβ, Qα = Zα and the corrected Vβ = Qβ. The beta core has central
derived subgroup equal to its embedded Frattini subgroup, and its literal
quotient by Zβ is elementary abelian of order 16.

The final two applications discharge the alpha-core premise in the existing
seed and original-Sylow counts. They retain only |Zβ| = 2 as the remaining
numerical premise, in addition to the commuting distance-one branch. The
full original Borel and the reduced-to-original transport are preserved.
The source profiles, odd five-path stabilizers and marked recognition are
not asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3), (11.6), (11.7)(c,e), printed pp.168--175, and (15.1), p.226.
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

/-- The actual reduced mixed cores and their Frattini and derived layers. -/
theorem mixed_binary_graph_core_structure (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥) :
    neighborCoreIntersection F β = Z F β ∧ Q F α = Z F α ∧
      betaSpan (stabilizer F β) (Z F α) = Q F β ∧
      (frattini (Q F β)).map (Q F β).subtype = ⁅Q F β,Q F β⁆ ∧
      ⁅Q F β,Q F β⁆ ≤ Z F β ∧ ⁅⁅Q F β,Q F β⁆,Q F β⁆ = ⊥ := by
  obtain ⟨c,hbc,hac,g,hga,hgb⟩ := mixed_turn K U₀ S h eK eU hc hb
  have ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hcard := mixed_reduced_neighbor_cards K U₀ S h eK eU β
  let e := mixed_alpha_marking K U₀ S h eK eU
  have hI := source_cubic_a5_neighbor_intersection_eq_center ht hB hS hc hb hcomm hbc hac hcard
    e g hga hgb
  have hQa := source_cubic_a5_core_eq_center_of_intersection ht hB hS hc hb hcomm hbc hac hcard e hI
  have hs := source_cubic_a5_beta_core_structure ht hB hS hc hb hcomm hbc hac hcard e g hga hgb
  exact ⟨hI,hQa,hs.2⟩

/-- The beta core has sixteen times the order of its actual beta center. -/
theorem mixed_binary_graph_beta_core_card_ratio (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥) :
    Nat.card (Q F β) = 16 * Nat.card (Z F β) := by
  obtain ⟨c,hbc,hac,_⟩ := mixed_turn K U₀ S h eK eU hc hb
  have ht := Reduction.reduced_triple h
  have hab := source_critical_one_adjacent hc hb
  have hQa := (mixed_binary_graph_core_structure K U₀ S h eK eU hc hb hcomm).2.1
  have hpair := beta_core_eq_pairSpan_of_alpha_core_eq _ _ _ _
    (mixed_binary_graph_core_generation K U₀ S h eK eU hc hb c hbc hac) hQa
  have hratio := source_cubic_a5_center_card_ratio ht (Reduction.reduced_borel_core_sylow h)
    (Reduction.reduced_vertex_sylow h) hc hb hcomm hbc hac
    (mixed_reduced_neighbor_cards K U₀ S h eK eU β) (mixed_alpha_marking K U₀ S h eK eU)
  change Nat.card (Z F α) = 8 * Nat.card (Z F β) at hratio
  let E := Z F α ⊓ Q F β
  let C := Z F c ⊓ Q F β
  have hindex := mixed_binary_graph_seed_index K U₀ S h eK eU hc hb
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup M) E (Z F α) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hindex,hratio] at hcount
  have hE : Nat.card E = 4 * Nat.card (Z F β) := by omega
  obtain ⟨g,_,_,_,hg⟩ := source_neighbor_conjugate ht hab hbc
  change E.map (MulAut.conj g).toMonoidHom = C at hg
  have hC : Nat.card C = 4 * Nat.card (Z F β) := by
    rw [←hg,card_map_of_injective (MulAut.conj g).injective,hE]
  have hn : Q F β ≤ normalizer (E : Set M) :=
    (le_inf (source_adjacent_core_normalizes_center ht hab) (Q F β).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes E C (inf_le_right.trans hn)
  have hinter : E ⊓ C = Z F β :=
    (mixed_binary_graph_center_intersections K U₀ S h eK eU hc hb hcomm c hbc hac).2.2.2
  change Q F β = E ⊔ C at hpair
  rw [hE,hC,hinter,←hpair] at hprod
  have hpos : 0 < Nat.card (Z F β) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  nlinarith

/-- The actual quotient Qβ/Zβ is elementary of order 16. -/
theorem mixed_binary_graph_beta_core_quotient (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥) :
    ∃ hN : ((Z F β).subgroupOf (Q F β)).Normal,
      letI := hN
      Nat.card (Q F β ⧸ (Z F β).subgroupOf (Q F β)) = 16 ∧
        IsElementaryAbelian 2 (Q F β ⧸ (Z F β).subgroupOf (Q F β)) := by
  have ht := Reduction.reduced_triple h
  have hZQ : Z F β ≤ Q F β := (source_Z_Q_U ht β).1.trans (map_subtype_le _)
  have hn : Q F β ≤ normalizer (Z F β : Set M) := (Q_le_stabilizer _ β).trans
    ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ β)).mp (Z_normal _ β))
  let hN : ((Z F β).subgroupOf (Q F β)).Normal := normal_subgroupOf_of_le_normalizer hn
  let := hN
  refine ⟨hN,?_,?_⟩
  · have hratio := mixed_binary_graph_beta_core_card_ratio K U₀ S h eK eU hc hb hcomm
    have hcount := card_eq_card_quotient_mul_card_subgroup ((Z F β).subgroupOf (Q F β))
    have hZcard : Nat.card ((Z F β).subgroupOf (Q F β)) = Nat.card (Z F β) :=
      Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv
    rw [hZcard,hratio] at hcount
    have hpos : 0 < Nat.card (Z F β) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos hcount.symm
  · have hs := (mixed_binary_graph_core_structure K U₀ S h eK eU hc hb hcomm).2.2.2
    exact @elementary_quotient_of_frattini_le (Q F β) _ _ 2 _
      (isPGroup_pCoreIn 2 (stabilizer F β)) ((Z F β).subgroupOf (Q F β)) hN
      (map_le_iff_le_comap.mp (hs.1.trans_le hs.2.1))

/-- The original mixed center layers have orders at most eight and 64. -/
theorem mixed_binary_graph_center_card_bounds (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥) :
    Nat.card (Z F β) ≤ 8 ∧ Nat.card (Z F α) ≤ 64 := by
  obtain ⟨c,hbc,hac,g,hga,hgb⟩ := mixed_turn K U₀ S h eK eU hc hb
  exact source_cubic_a5_center_card_bounds (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hc hb hcomm hbc hac (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
    (mixed_alpha_marking K U₀ S h eK eU) g hga hgb

/-- Only the remaining beta-center order is needed for the exact local orders. -/
theorem mixed_binary_graph_local_orders_of_beta_center_order (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (hZb : Nat.card (Z F β) = 2) :
    Q F α = Z F α ∧ betaSpan (stabilizer F β) (Z F α) = Q F β ∧
      Nat.card (Z F α) = 16 ∧ Nat.card (Z F α ⊓ Q F β : Subgroup M) = 8 ∧
      Nat.card (Q F β) = 32 := by
  obtain ⟨c,hbc,hac,_⟩ := mixed_turn K U₀ S h eK eU hc hb
  obtain ⟨_,hQa,hV,_⟩ := mixed_binary_graph_core_structure K U₀ S h eK eU hc hb hcomm
  have hinter : Nat.card ((Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) : Subgroup M) = 2 := by
    rw [(mixed_binary_graph_center_intersections K U₀ S h eK eU hc hb hcomm c hbc hac).2.2.2]
    exact hZb
  exact ⟨hQa,hV,mixed_binary_graph_seed_orders_of_intersection K U₀ S h eK eU hc hb c hbc hac hQa hinter⟩

/-- The literal mixed-size consumer with its alpha-core premise discharged. -/
theorem mixed_binary_graph_row_size_of_beta_center_order (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (hZb : Nat.card (Z F β) = 2) :
    Nat.card (twoCore (commonBorel ![K,U₀] S)) = 64 ∧
      (Nat.card S = 64 ∨ Nat.card S = 128) := by
  obtain ⟨c,hbc,hac,_⟩ := mixed_turn K U₀ S h eK eU hc hb
  exact mixed_binary_graph_row_size_of_center_order K U₀ S h eK eU hc hb hcomm c hbc hac
    (mixed_binary_graph_core_structure K U₀ S h eK eU hc hb hcomm).2.1 hZb

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
