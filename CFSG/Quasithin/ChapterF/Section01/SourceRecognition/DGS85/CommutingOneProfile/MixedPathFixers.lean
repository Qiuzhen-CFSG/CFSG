module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FiveEdgeFixers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedCenterOrder
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# Odd long-path fixers for the original mixed pair

Transport the original critical edge and its A₅ quotient marking to the
middle of a five-edge walk. The six-vertex fixer theorem gives odd order;
reversal handles the other orientation. Prefix containment then gives odd
fixers for every longer nonbacktracking walk, including closed source
paths. Thus actual four-path radicals act freely at each new exit, as
used by the regular apartment argument.

The full original A₅/S₃ data and the literal reduced graph are retained.
Path transitivity, the exact extrema r=4 and s=5, and transport to the
universal completion remain further steps; no ambient recognition is
inferred from these fixer orders.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.7)(f), printed pp.174--175, and (14.1), printed p.210.
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

open SimpleGraph SimpleGraph.Walk Theory.GroupTheory.WeakBNPair.RegularTree

private theorem mixed_edge_branch (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    {a b : Vertex F} (hab : (graph F).Adj a b) (ha : a.type = false) :
    IsCriticalPair F a b ∧ ⁅Z F a,Z F b⁆ = ⊥ ∧
      Nonempty ((stabilizer F a ⧸ pCore 2 (stabilizer F a)) ≃* alternatingGroup (Fin 5)) := by
  have hb : b.type = true := by
    have hn := hab.1
    rw [ha] at hn
    cases he : b.type <;> simp_all
  obtain ⟨g,hga,hgb⟩ := incident_common_translate F hab.2
  rw [ha] at hga
  rw [hb] at hgb
  have hc' := CommutingNontrivial.criticalPair_translate F hc g
  rw [hga,hgb] at hc'
  have hm := CommutingNontrivial.commuting_centers_translate F α β g
  rw [hga,hgb,hcomm,Subgroup.map_bot] at hm
  have hs : stabilizer F a = (stabilizer F α).map (MulAut.conj g).toMonoidHom := by
    rw [←hga,stabilizer_translate]
  let es := (MulEquiv.subgroupCongr hs).trans
    ((stabilizer F α).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  exact ⟨hc',hm,⟨(QuotientGroup.congr _ _ es (pCore_map_iso 2 es)).trans
    (mixed_alpha_marking K U₀ S h eK eU)⟩⟩

private theorem mixed_five_walk_odd_oriented (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    {a b : Vertex F} (p : (graph F).Walk a b) (hlen : p.length = 5)
    (hnb : ∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2))
    (ha : (p.getVert 2).type = false) :
    Odd (Nat.card (pathFixer (X := M) p)) := by
  have hadj (i : ℕ) (hi : i < 5) := p.adj_getVert_succ (by omega : i < p.length)
  obtain ⟨hc',hm,⟨e⟩⟩ := mixed_edge_branch K U₀ S h eK eU hc hcomm (hadj 2 (by decide)) ha
  have ht : (p.getVert 3).type = true := by
    have hh := (hadj 2 (by decide)).1
    rw [ha] at hh
    cases he : (p.getVert 3).type <;> simp_all
  have hcard : Nat.card ((graph F).neighborSet (p.getVert 3)) = 3 := by
    have hh := mixed_reduced_neighbor_cards K U₀ S h eK eU (p.getVert 3)
    simpa [ht] using hh
  have ho := source_cubic_a5_five_edge_fixer_odd (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    (hadj 0 (by decide)) (hadj 1 (by decide)) hc' hb hm
    (hadj 3 (by decide)) (hadj 4 (by decide))
    (hnb 0 (by omega)) (hnb 1 (by omega)) (hnb 2 (by omega)) (hnb 3 (by omega)) hcard e
  apply Odd.of_dvd_nat ho
  apply card_dvd_of_le
  intro x hx
  exact ⟨⟨⟨⟨⟨hx 0 (by omega),hx 1 (by omega)⟩,hx 2 (by omega)⟩,
    hx 3 (by omega)⟩,hx 4 (by omega)⟩,hx 5 (by omega)⟩

/-- Odd length-five fixers on the literal original reduced graph, in both
vertex orientations and with only consecutive backtracking excluded. -/
theorem mixed_binary_graph_five_walk_fixer_odd (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    {a b : Vertex F} (p : (graph F).Walk a b) (hlen : p.length = 5)
    (hnb : ∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2)) :
    Odd (Nat.card (pathFixer (X := M) p)) := by
  by_cases ht : (p.getVert 2).type = false
  · exact mixed_five_walk_odd_oriented K U₀ S h eK eU hc hb hcomm p hlen hnb ht
  have ht3 : (p.getVert 3).type = false := by
    have hh := (p.adj_getVert_succ (by omega : 2 < p.length)).1
    cases h2 : (p.getVert 2).type <;> cases h3 : (p.getVert 3).type <;> simp_all
  have hnb' : ∀ i, i+2 ≤ p.reverse.length →
      p.reverse.getVert i ≠ p.reverse.getVert (i+2) := by
    intro i hi
    rw [length_reverse,hlen] at hi
    simp only [getVert_reverse,hlen]
    convert (hnb (3-i) (by omega)).symm using 1 <;> congr 1 <;> omega
  have ho := mixed_five_walk_odd_oriented K U₀ S h eK eU hc hb hcomm p.reverse
    (by rwa [length_reverse]) hnb' (by simpa only [getVert_reverse,hlen] using ht3)
  rwa [pathFixer_reverse] at ho

/-- Every longer nonbacktracking walk has odd pointwise fixer. This includes
closed source paths and does not assume that the source graph is a tree. -/
theorem mixed_binary_graph_long_walk_fixer_odd (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    {a b : Vertex F} (p : (graph F).Walk a b) (hlen : 5 ≤ p.length)
    (hnb : ∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2)) :
    Odd (Nat.card (pathFixer (X := M) p)) := by
  have ht : (p.take 5).length = 5 := by rw [take_length,Nat.min_eq_left hlen]
  have ho := mixed_binary_graph_five_walk_fixer_odd K U₀ S h eK eU hc hb hcomm (p.take 5) ht (by
    intro i hi
    rw [ht] at hi
    simpa only [take_getVert, Nat.min_eq_right (show i ≤ 5 by omega),
      Nat.min_eq_right (show i+2 ≤ 5 by omega)] using hnb i (by omega))
  apply Odd.of_dvd_nat ho
  apply card_dvd_of_le
  intro x hx i hi
  rw [take_getVert]
  exact hx _ (Nat.min_le_left _ _ |>.trans hlen)

/-- The literal five-path premise consumed by the regular apartment argument. -/
theorem mixed_binary_graph_five_path_fixer_odd (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    {a b : Vertex F} (p : (graph F).Walk a b) (hp : p.IsPath) (hlen : 5 ≤ p.length) :
    Odd (Nat.card (pathFixer (X := M) p)) :=
  mixed_binary_graph_long_walk_fixer_odd K U₀ S h eK eU hc hb hcomm p hlen (by
    intro i hi he
    have hh := hp.getVert_injOn (by omega : i ≤ p.length) hi he
    omega)

/-- The genuine four-path radical acts freely at every new exit. This
supplies the odd-extension premise used in the regular apartment argument,
without assuming that the original graph is a tree. -/
theorem mixed_binary_graph_four_path_root_free (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    {a b c : Vertex F} (p : (graph F).Walk a b) (hp : p.IsPath) (hlen : p.length = 4)
    (hbc : (graph F).Adj b c) (hnew : c ∉ p.support) :
    pathRoot (X := M) p ⊓ MulAction.stabilizer M c = ⊥ ∧
      Function.Injective (fun x : pathRoot (X := M) p => (x : M) • c) := by
  have ho := mixed_binary_graph_five_path_fixer_odd K U₀ S h eK eU hc hb hcomm
    (p.concat hbc) (hp.concat hnew hbc) (by rw [length_concat,hlen])
  exact ⟨pathRoot_inf_stabilizer_eq_bot p hbc ho,pathRoot_smul_injective p hbc ho⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
