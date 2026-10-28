module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CubicGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CubicSeedIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedSeedApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedGraphApplication
public import Theory.GroupTheory.PCoreInRestriction

/-!
# Cubic generation and index on the original mixed-pair graph

The original A₅/S₃ quotient markings give the reduced beta vertex valence
three. The genuine reduced kernel Sylow then gives seed index two, and
two neighboring seeds generate the corrected Chapter 11 Vβ. The actual
quotient S₀/Qβ has order two and is elementary, selecting the (11.7) branch.
The derived subgroup of Vβ equals its Frattini subgroup and is central. These
statements use the actual reduced completion and its original vertex marks.

The index and the full reduced Borel-core product are discharged in the
literal mixed-pair count. Comparing the existing A₅ core ratio with the
two-seed product also determines center order sixteen and seed order eight.
The seed-intersection order, alpha-core equality, and core generation
remain explicit earlier Chapter 11 obligations. The numerical application
does not assert the full source profile or identify a unitary amalgam.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.3), (11.6), (11.7)(c), printed pp.168--175; reduction (15.1), p.226.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Source (6.2)(d) discharges the full kernel premise of the cubic seed index. -/
theorem reduced_cubic_seed_index (h : HypothesisF11 L S)
    {a b : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a b)
    (hb : DGS85.b (Reduction.reducedFamily L S) = 1)
    (hcard : Nat.card ((graph (Reduction.reducedFamily L S)).neighborSet b) = 3) :
    (Z (Reduction.reducedFamily L S) a ⊓ Q (Reduction.reducedFamily L S) b).relIndex
      (Z (Reduction.reducedFamily L S) a) = 2 :=
  source_cubic_seed_index (Reduction.reduced_triple h) hc hb hcard
    (Reduction.reduced_kernel_sylow h b)

variable [Finite G] (K U₀ S : Subgroup G)
local notation "F" => Reduction.reducedFamily ![K,U₀] S
local notation "M" => Reduction.G₀ ![K,U₀] S
local notation "R₀" => Subgroup.subgroupOf (twoCore (commonBorel ![K,U₀] S)) M
local notation "α" => base F false
local notation "β" => base F true

/-- The original mixed markings imply index two in the actual corrected seed. -/
theorem mixed_binary_graph_seed_index (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) :
    (Z F α ⊓ Q F β).relIndex (Z F α) = 2 :=
  reduced_cubic_seed_index h hc hb (mixed_reduced_neighbor_cards K U₀ S h eK eU β)

omit [Finite G] in
private theorem mixed_base_edge_core_eq_borel_core (h : HypothesisF11 ![K,U₀] S) :
    (stabilizer F α ⊓ stabilizer F β).pCoreIn 2 = R₀ := by
  have ht := Reduction.reduced_triple h
  have hBG : Reduction.B₀ ![K,U₀] S ≤ M :=
    (show Reduction.B₀ ![K,U₀] S ≤ Reduction.P₀ ![K,U₀] S 0 from le_sup_right).trans le_sup_left
  rw [show stabilizer F α = F false from Subgroup.CosetGeometry.stabilizer_base _ _,
    show stabilizer F β = F true from Subgroup.CosetGeometry.stabilizer_base _ _,
    show F false ⊓ F true = (Reduction.B₀ ![K,U₀] S).subgroupOf M from ht.intersection,
    pCoreIn_subgroupOf 2 _ _ hBG, Reduction.B₀_core h]
  rfl

/-- The full reduced Borel radical is Zα Qβ inside the actual reduced completion.
This strengthens the cubic (11.4) identity through the original inclusion. -/
theorem mixed_binary_graph_borel_core_supplement (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) :
    R₀ = Z F α ⊔ Q F β := by
  rw [←mixed_base_edge_core_eq_borel_core K U₀ S h]
  exact source_cubic_edge_core_eq_center_sup_core (Reduction.reduced_triple h) hc hb
    (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
    (Reduction.reduced_kernel_sylow h β)

/-- The exact two-core product in (11.4), with the literal reduced Borel radical. -/
theorem mixed_binary_graph_borel_core_product (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) :
    R₀ = Q F α ⊔ Q F β := by
  rw [←mixed_base_edge_core_eq_borel_core K U₀ S h]
  exact source_cubic_edge_core_eq_cores (Reduction.reduced_triple h) hc hb
    (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
    (Reduction.reduced_kernel_sylow h β)

/-- The literal S₀/Qβ is elementary of order two. This selects the (11.7)
branch at the cubic vertex; it does not assert its later structure conclusions. -/
theorem mixed_binary_graph_beta_quotient (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) :
    ∃ hN : ((Q F β).subgroupOf R₀).Normal,
      letI := hN
      Nat.card (R₀ ⧸ (Q F β).subgroupOf R₀) = 2 ∧
        IsElementaryAbelian 2 (R₀ ⧸ (Q F β).subgroupOf R₀) := by
  rw [←mixed_base_edge_core_eq_borel_core K U₀ S h]
  exact source_cubic_edge_core_quotient (Reduction.reduced_triple h) hc hb
    (mixed_reduced_neighbor_cards K U₀ S h eK eU β)
    (Reduction.reduced_kernel_sylow h β)

/-- The literal center pair is transitive and its two seeds fill Chapter 11 Vβ. -/
theorem mixed_binary_graph_seed_generation (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (c : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c) :
    (∀ w, (graph F).Adj β w → ∃ g ∈ Z F α ⊔ Z F c, g • α = w) ∧
      betaSpan (stabilizer F β) (Z F α) = pairSpan (Z F α) (Z F c) (Q F β) := by
  have ht := Reduction.reduced_triple h
  have hcard : Nat.card ((graph F).neighborSet β) = 3 :=
    mixed_reduced_neighbor_cards K U₀ S h eK eU β
  exact ⟨source_cubic_center_pair_transitive ht hc hb hbc hac hcard,
    source_cubic_betaSpan_eq_pairSpan ht hc hb hbc hac hcard⟩

/-- The central derived and Frattini layers belong to the full corrected beta span. -/
theorem mixed_binary_graph_span_frattini (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (c : Vertex F) (hbc : (graph F).Adj β c) (hac : α ≠ c) :
    let W := betaSpan (stabilizer F β) (Z F α)
    ⁅W,W⁆ = ⁅Z F α ⊓ Q F β,Z F c ⊓ Q F β⁆ ∧
      (frattini W).map W.subtype = ⁅W,W⁆ ∧
      ⁅W,W⁆ ≤ Z F α ⊓ Z F c ∧ ⁅⁅W,W⁆,W⁆ = ⊥ :=
  source_cubic_betaSpan_commutator_frattini (Reduction.reduced_triple h) hc hb hbc hac
    (mixed_reduced_neighbor_cards K U₀ S h eK eU β)

private theorem mixed_base_core_card_ratio (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3)) :
    Nat.card R₀ = 4 * Nat.card (Q F α) := by
  have hRM : twoCore (commonBorel ![K,U₀] S) ≤ M :=
    (show twoCore (commonBorel ![K,U₀] S) ≤ Reduction.B₀ ![K,U₀] S from le_sup_right).trans
      ((show Reduction.B₀ ![K,U₀] S ≤ Reduction.P₀ ![K,U₀] S 0 from le_sup_right).trans le_sup_left)
  have hRcard : Nat.card R₀ = Nat.card (pCore 2 (commonBorel ![K,U₀] S)) :=
    (Nat.card_congr (subgroupOfEquivOfLe hRM).toEquiv).trans
      (card_map_of_injective (commonBorel ![K,U₀] S).subtype_injective)
  have hQmap : (Q F α).map (M).subtype = twoCore (parabolic ![K,U₀] S 0) := by
    change ((stabilizer F α).pCoreIn 2).map (M).subtype = _
    rw [show stabilizer F α = F false from Subgroup.CosetGeometry.stabilizer_base _ _]
    change (((Reduction.P₀ ![K,U₀] S 0).subgroupOf M).pCoreIn 2).map (M).subtype = _
    rw [map_pCoreIn_of_injective 2 _ _ (M).subtype_injective,
      map_subgroupOf_eq_of_le (show Reduction.P₀ ![K,U₀] S 0 ≤ M from le_sup_left),
      Reduction.P₀_core h 0]
    rfl
  have hQcard : Nat.card (Q F α) = Nat.card (pCore 2 (parabolic ![K,U₀] S 0)) := by
    calc
      _ = Nat.card ((Q F α).map (M).subtype) := (card_map_of_injective (M).subtype_injective).symm
      _ = Nat.card (twoCore (parabolic ![K,U₀] S 0)) := congrArg (fun A : Subgroup G => Nat.card A) hQmap
      _ = _ := card_map_of_injective (parabolic ![K,U₀] S 0).subtype_injective
  rw [hRcard,hQcard]
  exact h.mixed_borel_core_card eK eU

/-- Comparing the A₅ Borel-core ratio with the two-seed product determines
the actual center, seed, and beta-core orders. No absolute order is assumed;
the earlier core identities and seed-intersection order remain explicit. -/
theorem mixed_binary_graph_seed_orders (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (c : Vertex F) (hbc : (graph F).Adj β c)
    (hgen : Q F β = pairSpan (Z F α) (Z F c) (Q F β) ⊔ (Q F α ⊓ Q F β))
    (hQa : Q F α = Z F α)
    (hinter : Nat.card ((Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) : Subgroup M) = 2) :
    Nat.card (Z F α) = 16 ∧ Nat.card (Z F α ⊓ Q F β : Subgroup M) = 8 ∧
      Nat.card (Q F β) = 32 := by
  have ht := Reduction.reduced_triple h
  have hab : (graph F).Adj α β := source_critical_one_adjacent hc hb
  let E := Z F α ⊓ Q F β
  let C := Z F c ⊓ Q F β
  have hindex := mixed_binary_graph_seed_index K U₀ S h eK eU hc hb
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup M) E (Z F α) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hindex] at hcount
  obtain ⟨g,_,_,_,hg⟩ := source_neighbor_conjugate ht hab hbc
  change E.map (MulAut.conj g).toMonoidHom = C at hg
  have hconj : Nat.card C = Nat.card E := by
    rw [←hg,card_map_of_injective (MulAut.conj g).injective]
  have hn : Q F β ≤ normalizer (E : Set M) :=
    (le_inf (source_adjacent_core_normalizes_center ht hab) (Q F β).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes E C (inf_le_right.trans hn)
  have hpair : Q F β = E ⊔ C := beta_core_eq_pairSpan_of_alpha_core_eq _ _ _ _ hgen hQa
  rw [hconj,hinter,←hpair] at hprod
  obtain ⟨hN,hquot,_⟩ := mixed_binary_graph_beta_quotient K U₀ S h eK eU hc hb
  let := hN
  have hqR : Q F β ≤ R₀ :=
    (mixed_binary_graph_borel_core_supplement K U₀ S h eK eU hc hb) ▸ le_sup_right
  have hindexQ : (Q F β).relIndex R₀ = 2 := hquot
  have hcountQ := relIndex_mul_relIndex (⊥ : Subgroup M) (Q F β) R₀ bot_le hqR
  rw [relIndex_bot_left,relIndex_bot_left,hindexQ] at hcountQ
  have hratio := mixed_base_core_card_ratio K U₀ S h eK eU
  rw [hQa] at hratio
  have hpos : 0 < Nat.card E := Nat.card_pos
  have he : Nat.card E = 8 := by nlinarith
  exact ⟨by omega,he,by nlinarith⟩


/-- In the mixed count the relative index and Borel-core product are now theorems of the source graph.
The earlier core identities and seed-intersection order remain explicit local obligations. -/
theorem mixed_binary_graph_row_size_of_cubic (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1)
    (c : Vertex F) (hbc : (graph F).Adj β c)
    (hgen : Q F β = pairSpan (Z F α) (Z F c) (Q F β) ⊔ (Q F α ⊓ Q F β))
    (hQa : Q F α = Z F α)
    (hinter : Nat.card ((Z F α ⊓ Q F β) ⊓ (Z F c ⊓ Q F β) : Subgroup M) = 2) :
    Nat.card (twoCore (commonBorel ![K,U₀] S)) = 64 ∧
      (Nat.card S = 64 ∨ Nat.card S = 128) := by
  have hR : R₀ = Q F α ⊔ Q F β :=
    mixed_binary_graph_borel_core_product K U₀ S h eK eU hc hb
  have hZ := (mixed_binary_graph_seed_orders K U₀ S h eK eU hc hb c hbc hgen hQa hinter).1
  exact mixed_binary_graph_row_size K U₀ S h eK eU c hbc hR hgen hQa hZ
    (mixed_binary_graph_seed_index K U₀ S h eK eU hc hb) hinter

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
