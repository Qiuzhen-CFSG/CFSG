module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedTerminal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.TorusKernels

/-!
# Full-Cartan centralizers in nonbinary local cores

A two-subgroup centralizing a full edge Cartan propagates from one vertex
core into the next. The next intrinsic torus is nontrivial and meets its
own permutation kernel trivially. The existing second-neighbor argument
therefore rules out a nontrivial image of the two-subgroup there.

The same Cartan extends to nonbacktracking paths of arbitrary length.
Propagation makes its initial core centralizer fix every vertex of such a
path. An odd long-path fixer consequently forces that centralizer to be
trivial. This is the nonbinary local input for the reflection lift in DGS
(14.2), printed pp.210--211; binary endpoints require a different argument.
-/

@[expose] public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.ApartmentExchange
open CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The whole Cartan propagates its commuting two-subgroup through a
nonbinary adjacent local quotient. -/
theorem full_cartan_centralizer_le_neighbor_core
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (ht : RootPathTransitive (graph (family P)) G v 2)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,k))
    (hk : 4 ≤ Nat.card k) (C A : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hAQ : A ≤ Q (family P) v) (hAC : A ≤ centralizer (C : Set G)) :
    A ≤ Q (family P) w := by
  let T := C ⊓ graphLocalGroup (family P) w
  have hCE' : C ≤ stabilizer (family P) w ⊓ stabilizer (family P) v :=
    hCE.trans (inf_comm _ _).le
  obtain ⟨⟨f⟩,_⟩ := edge_complement_local_torus h hB hS hvw.symm e C hCE'
    (by simpa only [inf_comm] using hd) (by simpa only [inf_comm] using hg)
  have hcard : 1 < Nat.card T := by
    rw [Nat.card_congr f.toEquiv,Nat.card_units]
    omega
  have hne : T ≠ ⊥ := by
    intro he
    rw [he,Subgroup.card_bot] at hcard
    omega
  have hCA := le_centralizer_iff.mp hAC
  exact cartan_centralizer_le_neighbor_core h hB hS hvw ht e C A T hCE hd hg hAQ
    (hCA.trans (Subgroup.centralizer_le_normalizer _)) inf_le_left hne
    (inf_le_left.trans hCA)
    (nonbinary_odd_torus_disjoint_kernel h hB hS hvw.symm e hk C ho)

private theorem endpoint_mem_vertices {v : Vertex (family P)} {n : ℕ}
    (p : BasedWalk (graph (family P)) n v) : p.endpoint ∈ p.vertices := by
  simpa only [support_toWalk] using p.toWalk.end_mem_support

private theorem penultimate_mem_vertices {v : Vertex (family P)} {n : ℕ}
    (p : BasedWalk (graph (family P)) (n+1) v) : p.penultimate ∈ p.vertices := by
  have hh := (p.take n (Nat.le_succ n)).toWalk.end_mem_support
  rw [support_toWalk,endpoint_take_penultimate,vertices_take] at hh
  exact List.mem_of_mem_take hh

/-- The prescribed full Cartan and any commuting subgroup of its initial
core fix one arbitrarily long nonbacktracking path. -/
theorem exists_full_cartan_core_fixed_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (ht : ∀ v : Vertex (family P), RootPathTransitive (graph (family P)) G v 2)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ v : Vertex (family P),
      (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,K v.type))
    (hK : ∀ i, 4 ≤ Nat.card (K i))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (C A : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (hAQ : A ≤ Q (family P) v) (hAC : A ≤ centralizer (C : Set G)) (n : ℕ) :
    ∃ p : BasedWalk (graph (family P)) (n+1) v,
      p.Nonbacktracking ∧ C ≤ pathStabilizer (family P) p ∧
      A ≤ pathStabilizer (family P) p ∧ A ≤ Q (family P) p.endpoint := by
  induction n with
  | zero =>
    let p : BasedWalk (graph (family P)) 1 v := ⟨⟨w,hvw⟩,PUnit.unit⟩
    have hAw : A ≤ Q (family P) w := full_cartan_centralizer_le_neighbor_core
      h hB hS hvw (ht v) (e w) (hK w.type) C A hCE ho hd hg hAQ hAC
    refine ⟨p,True.intro,?_,?_,hAw⟩
    · intro c hc z hz
      change z ∈ [v,w] at hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · exact (hCE hc).1
      · exact (hCE hc).2
    · intro a ha z hz
      change z ∈ [v,w] at hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · exact Q_le_stabilizer (family P) _ (hAQ ha)
      · exact Q_le_stabilizer (family P) _ (hAw ha)
  | succ n ih =>
    obtain ⟨p,hp,hCp,hAp,hAend⟩ := ih
    have hCE' : C ≤ stabilizer (family P) p.penultimate ⊓ stabilizer (family P) p.endpoint :=
      hCp.trans (pathStabilizer_le_edge (family P) p
        (penultimate_mem_vertices p) (endpoint_mem_vertices p))
    obtain ⟨hd',hg'⟩ := path_cartan_complement_at_edge h hvw p.adj_penultimate_endpoint
      C hCE hCE' ho hd hg
    obtain ⟨r,hr,hrne,hCr⟩ := edge_cartan_second_fixed_neighbor h hB hS
      p.adj_penultimate_endpoint (ht p.penultimate) C hCE' hd' hg'
    have hCE'' : C ≤ stabilizer (family P) p.endpoint ⊓ stabilizer (family P) r :=
      le_inf (hCE'.trans inf_le_right) hCr
    obtain ⟨hd'',hg''⟩ := path_cartan_complement_at_edge h hvw hr C hCE hCE'' ho hd hg
    have hAr : A ≤ Q (family P) r := full_cartan_centralizer_le_neighbor_core
      h hB hS hr (ht p.endpoint) (e r) (hK r.type) C A hCE'' ho hd'' hg'' hAend hAC
    refine ⟨p.snoc hr,(nonbacktracking_snoc_iff p hr).mpr ⟨hp,hrne⟩,?_,?_,?_⟩
    · intro c hc z hz
      rw [vertices_snoc,List.mem_append,List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hCp hc z hz
      · exact hCr hc
    · intro a ha z hz
      rw [vertices_snoc,List.mem_append,List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hAp ha z hz
      · exact Q_le_stabilizer (family P) _ (hAr ha)
    · simpa only [endpoint_snoc] using hAr

/-- An odd long-path fixer kills the whole Cartan centralizer in either
incident vertex core, without assuming a chosen reflection. -/
theorem full_cartan_core_centralizer_eq_bot
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (ht : ∀ v : Vertex (family P), RootPathTransitive (graph (family P)) G v 2)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ v : Vertex (family P),
      (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,K v.type))
    (hK : ∀ i, 4 ≤ Nat.card (K i))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (C : Subgroup G) [IsMulCommutative C]
    (hCE : C ≤ stabilizer (family P) v ⊓ stabilizer (family P) w)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 =
      stabilizer (family P) v ⊓ stabilizer (family P) w)
    (n : ℕ)
    (hodd : ∀ p : BasedWalk (graph (family P)) (n+1) v,
      p.Nonbacktracking → Odd (Nat.card (pathStabilizer (family P) p))) :
    Q (family P) v ⊓ centralizer (C : Set G) = ⊥ := by
  let _ := finite_endpoints h
  let A := Q (family P) v ⊓ centralizer (C : Set G)
  let _ : Finite A := Finite.of_injective
    (inclusion (inf_le_left.trans (Q_le_stabilizer (family P) v))) (inclusion_injective _)
  obtain ⟨p,hp,_,hAp,_⟩ := exists_full_cartan_core_fixed_path
    h hB hS ht K e hK hvw C A hCE ho hd hg inf_le_left inf_le_right n
  have hpA : IsPGroup 2 A := (isPGroup_pCoreIn 2 _).to_le inf_le_left
  have hoA : Odd (Nat.card A) := (hodd p hp).of_dvd_nat (card_dvd_of_le hAp)
  obtain ⟨m,hm⟩ := hpA.exists_card_eq
  have hone : Nat.card A = 1 := by
    have hc := hoA.coprime_two_right.pow_right m
    rw [←hm] at hc
    exact Nat.eq_one_of_dvd_coprimes hc dvd_rfl dvd_rfl
  exact Subgroup.eq_bot_of_card_eq A hone

end CFSG.Quasithin.ChapterF.Source.DGS85.ApartmentExchange
