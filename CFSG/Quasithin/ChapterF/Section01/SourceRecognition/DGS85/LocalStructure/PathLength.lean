module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathKernel
public import BenderSuzuki.Converse.PSL2

/-!
# Excluding short nontransitive linear paths

Two distinct incident edge stabilizers generate the full vertex stabilizer:
otherwise their equal orders make them equal, and the edge-core normalizer
identity would identify their fixed neighbors. Conjugation also gives equal
orders for core intersections at all edges.

For a three-edge path, Q₁ intersect Q₂ lies normally in the path fixer.
Endpoint core containment puts it in Q₃, so equal orders identify it with
Q₂ intersect Q₃. Both incident edge stabilizers then normalize this common
intersection, contradicting 6.5(a). The one- and two-edge cases give shorter
contradictions. Combining these arguments with the linear endpoint theorem
proves both conclusions of 6.8, conditional on the still-open 6.5 obstruction
and the earlier path inputs. The actual reduced F1.11 application transports
the path core through the original completion inclusion.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 6.8(a,b), pp.123--124. This module does not discharge 6.5.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Distinct incident edges generate their full common vertex stabilizer. -/
theorem source_two_edges_generate (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v w z : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (hz : (graph (family P)).Adj v z) (hne : w ≠ z) :
    (stabilizer (family P) v ⊓ stabilizer (family P) w) ⊔
      (stabilizer (family P) v ⊓ stabilizer (family P) z) = stabilizer (family P) v := by
  let := finite_endpoints h
  let E := stabilizer (family P) v ⊓ stabilizer (family P) w
  let D := stabilizer (family P) v ⊓ stabilizer (family P) z
  have hneq : D ≠ E := by
    intro he
    obtain ⟨g,hg,hgz⟩ := locally_transitive (family P) hw hz
    have hm : E.map (MulAut.conj g).toMonoidHom = D := by
      rw [show E = stabilizer (family P) v ⊓ stabilizer (family P) w from rfl,
        Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← stabilizer_translate,
        ← stabilizer_translate]
      rw [show g • v = v from hg,hgz]
    have hcore : (E.pCoreIn 2).map (MulAut.conj g).toMonoidHom = E.pCoreIn 2 := by
      rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj g).injective,
        hm,he]
    have hn : g ∈ normalizer (E.pCoreIn 2 : Set G) := mem_normalizer_iff_map_conj_eq.mpr hcore
    have hge : g ∈ E := by
      change g ∈ stabilizer (family P) v ⊓ stabilizer (family P) w
      rw [← source_edge_core_normalizer h hB hw]
      exact ⟨hg,hn⟩
    exact hne (hge.2.symm.trans hgz)
  have hnot : ¬ D ≤ E := by
    intro hle
    apply hneq
    let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer (family P) v from inf_le_left))
      (inclusion_injective _)
    apply eq_of_le_of_card_ge hle
    rw [show D = stabilizer (family P) v ⊓ stabilizer (family P) z from rfl,
      show E = stabilizer (family P) v ⊓ stabilizer (family P) w from rfl,
      card_edgeStabilizer (family P) hw,card_edgeStabilizer (family P) hz]
  rcases source_edge_maximal h hw (E ⊔ D) le_sup_left (sup_le inf_le_left inf_le_left) with he | he
  · exact (hnot (le_sup_right.trans he.le)).elim
  · exact he

/-- The intersection of the actual cores has the same order at every edge. -/
theorem source_card_adjacent_core_inter
    {v w x y : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hxy : (graph (family P)).Adj x y) :
    Nat.card (Q (family P) v ⊓ Q (family P) w : Subgroup G) =
      Nat.card (Q (family P) x ⊓ Q (family P) y : Subgroup G) := by
  have hc {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
      Nat.card (Q (family P) a ⊓ Q (family P) b : Subgroup G) =
        Nat.card ((P 0).pCoreIn 2 ⊓ (P 1).pCoreIn 2 : Subgroup G) := by
    obtain ⟨g,ha,hb⟩ := incident_common_translate (family P) hab.2
    rw [← ha, ← hb,Q_translate,Q_translate,←Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      card_map_of_injective (MulAut.conj g).injective]
    have hq (i : Bool) : Q (family P) (base (family P) i) = (family P i).pCoreIn 2 := by
      change (MulAction.stabilizer G (Subgroup.CosetGeometry.base (family P) i)).pCoreIn 2 = _
      rw [Subgroup.CosetGeometry.stabilizer_base]
    rw [hq,hq]
    have hne := hab.1
    cases ha : a.type <;> cases hb : b.type
    · exact (hne (ha.trans hb.symm)).elim
    · rfl
    · rw [inf_comm]; rfl
    · exact (hne (ha.trans hb.symm)).elim
  exact (hc hvw).trans (hc hxy).symm

private theorem core_normalized (v : Vertex (family P)) :
    stabilizer (family P) v ≤ normalizer (Q (family P) v : Set G) :=
  (stabilizer (family P) v).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer (family P) v)))

/-- A length-one path cannot have its edge core trapped in the endpoint core. -/
theorem source_one_path_core_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v : Vertex (family P)} (p : BasedWalk (graph (family P)) 1 v)
    (hk : (pathStabilizer (family P) p).pCoreIn 2 ≤ Q (family P) p.endpoint) : False := by
  let w := (p.1 : Vertex (family P))
  have hvw : (graph (family P)).Adj v w := p.1.property
  let E := stabilizer (family P) w ⊓ stabilizer (family P) v
  have hpE : pathStabilizer (family P) p = E := by
    ext g
    change (∀ z ∈ [v,w], g • z = z) ↔ g ∈ E
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact and_comm
  have heQ : E.pCoreIn 2 = Q (family P) w := by
    apply le_antisymm (hpE ▸ hk)
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (stabilizer (family P) w))
      ((source_Z_Q_U h w).2.trans (ballKernel_one_le_edge (family P) hvw.symm))
      (inf_le_left.trans (core_normalized w))
  have he : E = stabilizer (family P) w := by
    apply le_antisymm inf_le_left
    intro g hg
    rw [←source_edge_core_normalizer h hB hvw.symm,heQ]
    exact ⟨hg,core_normalized w hg⟩
  obtain ⟨g,hP,hE⟩ := source_edge_transport h hvw.symm
  have hb : B = family P w.type := map_injective (MulAut.conj g).injective
    (hE.symm.trans (he.trans hP))
  cases hw : w.type
  · exact (source_borel_lt (Classical.choice (h.local_data 0))).ne (by rw [hw] at hb; exact hb)
  · exact (source_borel_lt (Classical.choice (h.local_data 1))).ne (by rw [hw] at hb; exact hb)

/-- Length two forces one vertex core into the next, contradicting 6.5(a). -/
theorem source_two_path_core_obstruction (h : LocallyRankOneTriple P B)
    {v : Vertex (family P)} (p : BasedWalk (graph (family P)) 2 v)
    (hk : (pathStabilizer (family P) p).pCoreIn 2 ≤ Q (family P) p.endpoint)
    (hob : ∀ a b : Vertex (family P), (graph (family P)).Adj a b →
      ¬ stabilizer (family P) a ≤ normalizer ((Q (family P) b ⊓ Q (family P) a : Subgroup G) : Set G)) :
    False := by
  let a := (p.1 : Vertex (family P))
  let b := (p.2.1 : Vertex (family P))
  have hab : (graph (family P)).Adj a b := p.2.1.property
  let H := pathStabilizer (family P) p
  have hQH : Q (family P) a ≤ H := by
    intro g hg z hz
    change z ∈ [v,a,b] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with hz | hz | hz <;> subst z
    · exact ((source_Z_Q_U h a).2 hg) v
        ((mem_ball_one (family P) a v).mpr (Or.inl p.1.property.symm))
    · exact Q_le_stabilizer _ a hg
    · exact ((source_Z_Q_U h a).2 hg) b
        ((mem_ball_one (family P) a b).mpr (Or.inl hab))
  have hn : H ≤ normalizer (Q (family P) a : Set G) :=
    (show H ≤ stabilizer (family P) a from fun g hg =>
      hg a (by change a ∈ [v,a,b]; simp)).trans (core_normalized a)
  have hQ : Q (family P) a ≤ Q (family P) b :=
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (stabilizer (family P) a)) hQH hn).trans hk
  apply hob a b hab
  rw [inf_eq_right.mpr hQ]
  exact core_normalized a

/-- The substantive length-three exclusion in 6.8(b), from the endpoint
core conclusion of (a) and the exact adjacent-core obstruction 6.5(a). -/
theorem source_three_path_core_obstruction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v : Vertex (family P)} (p : BasedWalk (graph (family P)) 3 v) (hp : p.Nonbacktracking)
    (hk : (pathStabilizer (family P) p).pCoreIn 2 ≤ Q (family P) p.endpoint)
    (hob : ∀ a b : Vertex (family P), (graph (family P)).Adj a b →
      ¬ stabilizer (family P) a ≤ normalizer ((Q (family P) b ⊓ Q (family P) a : Subgroup G) : Set G)) :
    False := by
  let a := (p.1 : Vertex (family P))
  let b := (p.2.1 : Vertex (family P))
  let c := (p.2.2.1 : Vertex (family P))
  have hab : (graph (family P)).Adj a b := p.2.1.property
  have hbc : (graph (family P)).Adj b c := p.2.2.1.property
  let I := Q (family P) a ⊓ Q (family P) b
  let J := Q (family P) b ⊓ Q (family P) c
  let H := pathStabilizer (family P) p
  have hIH : I ≤ H := by
    intro g hg z hz
    change z ∈ [v,a,b,c] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with hz | hz | hz | hz <;> subst z
    · exact ((source_Z_Q_U h a).2 hg.1) v
        ((mem_ball_one (family P) a v).mpr (Or.inl p.1.property.symm))
    · exact Q_le_stabilizer _ a hg.1
    · exact Q_le_stabilizer _ b hg.2
    · exact ((source_Z_Q_U h b).2 hg.2) c
        ((mem_ball_one (family P) b c).mpr (Or.inl hbc))
  have hnI : H ≤ normalizer (I : Set G) := by
    apply (le_inf _ _).trans inf_normalizer_le_normalizer_inf
    · exact (show H ≤ stabilizer (family P) a from fun g hg =>
        hg a (by change a ∈ [v,a,b,c]; simp)).trans (core_normalized a)
    · exact (show H ≤ stabilizer (family P) b from fun g hg =>
        hg b (by change b ∈ [v,a,b,c]; simp)).trans (core_normalized b)
  have hIc : I ≤ Q (family P) c :=
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (stabilizer (family P) a)).to_inf_left hIH hnI).trans hk
  have hIJ : I ≤ J := le_inf inf_le_right hIc
  let := finite_endpoints h
  let : Finite J := Finite.of_injective
    (inclusion (show J ≤ stabilizer (family P) b from inf_le_left.trans (Q_le_stabilizer _ b)))
    (inclusion_injective _)
  have he : I = J := eq_of_le_of_card_ge hIJ (source_card_adjacent_core_inter hab hbc).ge
  have hn : stabilizer (family P) b ≤ normalizer (I : Set G) := by
    rw [←source_two_edges_generate h hB hab.symm hbc hp.2.1.symm]
    apply sup_le
    · exact (le_inf (inf_le_right.trans (core_normalized a))
        (inf_le_left.trans (core_normalized b))).trans inf_normalizer_le_normalizer_inf
    · rw [he]
      exact (le_inf (inf_le_left.trans (core_normalized b))
        (inf_le_right.trans (core_normalized c))).trans inf_normalizer_le_normalizer_inf
  exact hob b a hab.symm hn

/-- The short-path exclusions assemble to the source lower bound in 6.8(b).
The remaining 6.5 obstruction is explicit and is not assumed proved here. -/
theorem source_path_length_ge_four_of_core (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v : Vertex (family P)} {n : ℕ}
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    (hk : (pathStabilizer (family P) p).pCoreIn 2 ≤ Q (family P) p.endpoint)
    (hob : ∀ a b : Vertex (family P), (graph (family P)).Adj a b →
      ¬ stabilizer (family P) a ≤ normalizer ((Q (family P) b ⊓ Q (family P) a : Subgroup G) : Set G)) :
    4 ≤ n+1 := by
  cases n with
  | zero => exact (source_one_path_core_obstruction h hB p hk).elim
  | succ n =>
    cases n with
    | zero => exact (source_two_path_core_obstruction h p hk hob).elim
    | succ n =>
      cases n with
      | zero => exact (source_three_path_core_obstruction h hB p hp hk hob).elim
      | succ n => omega

/-- Both conclusions of DGS 6.8 in the binary linear case. The source 6.5
obstruction and Chapter 3 path inputs remain explicit for final assembly. -/
theorem source_linear_path_conclusions (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    {v : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (family P) p.endpoint ⧸ pCore 2 (graphLocalGroup (family P) p.endpoint)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K)
    (hnot : ¬ ∀ x y : (graph (family P)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (family P) p, g • x.val = y.val)
    (hob : ∀ a b : Vertex (family P), (graph (family P)).Adj a b →
      ¬ stabilizer (family P) a ≤ normalizer ((Q (family P) b ⊓ Q (family P) a : Subgroup G) : Set G)) :
    (pathStabilizer (family P) p).pCoreIn 2 ≤ U (family P) p.endpoint ∧ 4 ≤ n+1 :=
  ⟨source_path_core_le_endpoint_kernel_of_quotient h hB hS hbranch ht p hp e hnot,
    source_path_length_ge_four_of_core h hB p hp
      (source_path_core_le_endpoint_core h hB hS hbranch ht p hp e hnot) hob⟩

/-- The projective linear alternative of source 6.8 uses the actual
characteristic-two special-to-projective isomorphism, retaining the field. -/
theorem source_projective_path_conclusions (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    {v : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (family P) p.endpoint ⧸ pCore 2 (graphLocalGroup (family P) p.endpoint)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (hnot : ¬ ∀ x y : (graph (family P)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (family P) p, g • x.val = y.val)
    (hob : ∀ a b : Vertex (family P), (graph (family P)).Adj a b →
      ¬ stabilizer (family P) a ≤ normalizer ((Q (family P) b ⊓ Q (family P) a : Subgroup G) : Set G)) :
    (pathStabilizer (family P) p).pCoreIn 2 ≤ U (family P) p.endpoint ∧ 4 ≤ n+1 := by
  let eSL : Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  exact source_linear_path_conclusions h hB hS hbranch ht p hp (e.trans eSL.symm) hnot hob

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The literal reduced F1.11 consumer of 6.8(a,b), with its actual endpoint
quotient. The remaining 6.5 obstruction is retained, not certified here. -/
theorem reduced_linear_path_conclusions (h : HypothesisF11 L S)
    (hbranch : ∀ i, ∃ k,
      ((reducedFamily L S (!i)).subgroupOf (reducedFamily L S i)).index - 1 = 2^k)
    {v : Vertex (reducedFamily L S)} {n : ℕ}
    (ht : RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v (n+1))
    (p : BasedWalk (graph (reducedFamily L S)) (n+1) v) (hp : p.Nonbacktracking)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (reducedFamily L S) p.endpoint ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) p.endpoint)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K)
    (hnot : ¬ ∀ x y : (graph (reducedFamily L S)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (reducedFamily L S) p, g • x.val = y.val)
    (hob : ∀ a b : Vertex (reducedFamily L S), (graph (reducedFamily L S)).Adj a b →
      ¬ stabilizer (reducedFamily L S) a ≤ normalizer
        ((Q (reducedFamily L S) b ⊓ Q (reducedFamily L S) a : Subgroup (G₀ L S)) : Set (G₀ L S))) :
    ((pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype).pCoreIn 2 ≤
        (U (reducedFamily L S) p.endpoint).map (G₀ L S).subtype ∧ 4 ≤ n+1 := by
  obtain ⟨hk,hn⟩ := source_linear_path_conclusions (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hbranch ht p hp e hnot hob
  refine ⟨?_,hn⟩
  rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective]
  exact map_mono hk

/-- The reduced F1.11 projective-linear application, with the original
inclusion, literal path core, and both conclusions of 6.8. -/
theorem reduced_projective_path_conclusions (h : HypothesisF11 L S)
    (hbranch : ∀ i, ∃ k,
      ((reducedFamily L S (!i)).subgroupOf (reducedFamily L S i)).index - 1 = 2^k)
    {v : Vertex (reducedFamily L S)} {n : ℕ}
    (ht : RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v (n+1))
    (p : BasedWalk (graph (reducedFamily L S)) (n+1) v) (hp : p.Nonbacktracking)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : (graphLocalGroup (reducedFamily L S) p.endpoint ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) p.endpoint)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (hnot : ¬ ∀ x y : (graph (reducedFamily L S)).neighborSet p.endpoint,
      x.val ≠ p.penultimate → y.val ≠ p.penultimate →
        ∃ g ∈ pathStabilizer (reducedFamily L S) p, g • x.val = y.val)
    (hob : ∀ a b : Vertex (reducedFamily L S), (graph (reducedFamily L S)).Adj a b →
      ¬ stabilizer (reducedFamily L S) a ≤ normalizer
        ((Q (reducedFamily L S) b ⊓ Q (reducedFamily L S) a : Subgroup (G₀ L S)) : Set (G₀ L S))) :
    ((pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype).pCoreIn 2 ≤
        (U (reducedFamily L S) p.endpoint).map (G₀ L S).subtype ∧ 4 ≤ n+1 := by
  obtain ⟨hk,hn⟩ := source_projective_path_conclusions (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hbranch ht p hp e hnot hob
  refine ⟨?_,hn⟩
  rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective]
  exact map_mono hk
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
