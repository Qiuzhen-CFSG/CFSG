module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ConstituentIndices

/-!
# The reciprocal Chapter 9 configuration at distance three

At b = 3 the two neighborhood vertices are distance two apart. Transport
the supplied alpha quotient to their common neighbor, then lift the linear
matrix exchange to the actual local group. This exchanges both vertices,
with square in the middle vertex core. It proves reverse escape, reverse
zero displacement, and equality of the original core indices. The linear
constituent bounds then identify those indices with the beta field order.

This supplies the b = 3 part of 9.6 and the corresponding 9.3(b) application
without Chapter 8 exchange or whole-residual descent premises. It retains
the supplied local markings; proving b = 3 and initial recognition remains
with the source assembly. No assumption that the graph is a tree is used.
Source: DGS, Groups and Graphs (1985), 9.2--9.3 and 9.6, pp.142--144.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The original linear actor at the middle of a distance-two pair contains
an exchange element whose square is in the actual middle core. -/
theorem linear_distance_two_exchange (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta a' : Vertex (family P)} (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' = 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eα : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,F)) :
    ∃ m : Vertex (family P), (graph (family P)).Adj beta m ∧ (graph (family P)).Adj m a' ∧
      ∃ t : graphLocalGroup (family P) m,
        (t : G) • beta = a' ∧ (t : G) • a' = beta ∧ (t : G) * t ∈ Q (family P) m := by
  let Γ := family P
  let : ∀ i, Finite (Γ i) := finite_endpoints h
  change (graph Γ).dist beta a' = 2 at hd
  have hne : beta ≠ a' := by
    intro he
    rw [he,SimpleGraph.dist_self] at hd
    omega
  obtain ⟨m,hma',hdm⟩ := exists_predecessor Γ h.generate beta a' hne
  have hbm : (graph Γ).Adj beta m := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  have htypes : a.type = m.type := by
    have ha := hab.1
    have hm := hbm.1
    cases ha' : a.type <;> cases hm' : m.type <;> cases hb' : beta.type <;> simp_all
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ a m).mpr htypes
  obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport h g hg
  obtain ⟨t,ht,ht',ht2⟩ := linear_local_neighbor_exchange h hB hS hbm.symm hma'.symm (f.symm.trans eα)
  exact ⟨m,hbm,hma'.symm,t,ht,ht',ht2⟩

variable {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Source 9.6 at b = 3: the small-neighbor containment is impossible.
The same exchange also supplies 9.2 and equality of the two literal indices. -/
theorem reduced_distance_three_reciprocal (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb3 : b (Reduction.reducedFamily L S₀) = 3)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    (¬ V Γ a' 1 ≤ Q Γ beta) ∧ ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ = ⊥ ∧
      (Q Γ a').relIndex (V Γ beta 1) = (Q Γ beta).relIndex (V Γ a' 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hdist : (graph (Reduction.reducedFamily L S₀)).dist beta a' = 2 := by omega
  obtain ⟨m,_,_,t,ht₁,ht₂,_⟩ := linear_distance_two_exchange (a' := a') ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hab hdist eα
  change (t : Reduction.G₀ L S₀) • beta = a' at ht₁
  change (t : Reduction.G₀ L S₀) • a' = beta at ht₂
  have hforward : ¬ V Γ beta 1 ≤ Q Γ a' :=
    V_not_le_Q_of_criticalPair Γ hc hab.symm (source_Z_Q_U ht a').2
  refine ⟨?_,reverse_commutator_eq_bot_of_exchange Γ htriv t ht₁ ht₂,?_⟩
  · intro he
    have hm := map_mono (f := (MulAut.conj (t : Reduction.G₀ L S₀)).toMonoidHom) he
    rw [←V_translate,←Q_translate] at hm
    have hv := congrArg (fun v => V Γ v 1) ht₂
    have hq := congrArg (fun v => Q Γ v) ht₁
    rw [hv,hq] at hm
    exact hforward hm
  · have hi := relIndex_map_map_of_injective
      (f := (MulAut.conj (t : Reduction.G₀ L S₀)).toMonoidHom) (Q Γ a') (V Γ beta 1)
      (MulAut.conj (t : Reduction.G₀ L S₀)).injective
    rw [←Q_translate,←V_translate] at hi
    have hv := congrArg (fun v => V Γ v 1) ht₁
    have hq := congrArg (fun v => Q Γ v) ht₂
    rw [hv,hq] at hi
    exact hi.symm

/-- At distance three, the actual original indices equal the beta field
order without a Chapter 8 exchange or residual-action-descent hypothesis. -/
theorem reduced_distance_three_linear_indices (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb3 : b (Reduction.reducedFamily L S₀) = 3)
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n)
    (eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2,F))
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,K)) :
    let Γ := Reduction.reducedFamily L S₀
    (¬ V Γ a' 1 ≤ Q Γ beta) ∧ ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ = ⊥ ∧
      (Q Γ a').relIndex (V Γ beta 1) = Nat.card K ∧
      (Q Γ beta).relIndex (V Γ a' 1) = Nat.card K := by
  let Γ := Reduction.reducedFamily L S₀
  have hb : 1 < b Γ := by change 1 < b (Reduction.reducedFamily L S₀); omega
  obtain ⟨he,hrev,hi⟩ := reduced_distance_three_reciprocal h hc hab hd hb3 htriv eα
  obtain ⟨hy,hx⟩ := reduced_critical_linear_constituent_field_bounds h hc hab hd hb hcomm he hn hK eβ
  have hc₀ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv)
  change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hc₀
  simp only [inf_relIndex_left] at hc₀
  rw [hc₀,hi] at hx
  exact ⟨he,hrev,hi.trans (le_antisymm hy hx),le_antisymm hy hx⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
