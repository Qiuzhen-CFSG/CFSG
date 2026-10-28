module
public import Theory.GroupTheory.AmalgamGraph.PathSupplement
public import Theory.GroupAction.CubicTree.ArcTransport

/-!
# The first nonregular path in a finite-local coset graph

If both valences are at least three, the number of nonbacktracking paths
exceeds any fixed finite vertex-stabilizer order. Orbit--stabilizer thus
forces a nonregular path. The first such length is positive; reversal
makes all shorter paths regular at both ends, and prefix induction gives
rooted transitivity through that length in both vertex orbits.

A common edge transporter places a failing path through the original base
edge, retaining its pointwise fixer. Neither the completion nor the graph
is assumed finite, and no tree hypothesis is used.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
Part II, the definition of s and 3.4, pp.73--74; used in 6.7--6.8, p.123.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

private theorem forwardCount_lower (degree : Bool → ℕ) (hd : ∀ i, 3 ≤ degree i)
    (n : ℕ) (i : Bool) : 2^n ≤ BasedWalk.forwardCount degree n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    change 2^(n+1) ≤ (degree i - 1) * BasedWalk.forwardCount degree n (!i)
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul (by have := hd i; omega) (ih (!i))

private theorem card_paths_lower [∀ i, Finite (F i)]
    (hd : ∀ i, 3 ≤ ((F (!i)).subgroupOf (F i)).index)
    (n : ℕ) (v : Vertex F) :
    3 * 2^n ≤ Nat.card {p : BasedWalk (graph F) (n+1) v // p.Nonbacktracking} := by
  let degree := fun i => ((F (!i)).subgroupOf (F i)).index
  let : ∀ v : Vertex F, Finite ((graph F).neighborSet v) := Theory.GroupTheory.AmalgamGraph.finite_neighbors F
  have hf : ∀ {v w : Vertex F}, (graph F).Adj v w → w.type = !v.type := by
    intro v w h
    have hn := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  rw [BasedWalk.card_nonbacktracking_succ (graph F) (fun v => v.type) degree hf
    (card_neighbors_of_indices F degree (fun _ => rfl))]
  exact Nat.mul_le_mul (hd _) (forwardCount_lower degree hd n _)

/-- Finite local groups prevent transitivity on paths of arbitrarily large length. -/
theorem exists_nonregular_path [∀ i, Finite (F i)]
    (hd : ∀ i, 3 ≤ ((F (!i)).subgroupOf (F i)).index) :
    ∃ n, ∃ v : Vertex F, ∃ p : BasedWalk (graph F) n v,
      p.Nonbacktracking ∧ ¬ RightRegular (A := G) p := by
  classical
  by_contra! hall
  let v := base F false
  let d := Nat.card (stabilizer F v)
  have hl := card_paths_lower F hd d v
  have hn : Nonempty {p : BasedWalk (graph F) (d+1) v // p.Nonbacktracking} :=
    (Nat.card_pos_iff.mp (lt_of_lt_of_le (by positivity) hl)).1
  obtain ⟨p,hp⟩ := hn
  have ha : GraphAction (graph F) G :=
    ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj h⟩
  have ht := rootPathTransitive_of_short_rightRegular ha (d+1)
    (fun n v p _ hp => hall n v p hp) v (d+1) le_rfl
  let : Finite (pathStabilizer F p) := Finite.of_injective
    (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
  have hcard := card_paths_mul_card_fixer F ht p hp
  have hle : Nat.card {p : BasedWalk (graph F) (d+1) v // p.Nonbacktracking} ≤ d := by
    calc
      _ ≤ Nat.card {p : BasedWalk (graph F) (d+1) v // p.Nonbacktracking} *
          Nat.card (pathStabilizer F p) := Nat.le_mul_of_pos_right _ Nat.card_pos
      _ = d := hcard
  have hpw : d < 2^d := Nat.lt_two_pow_self
  omega

/-- The first nonregular length is positive and all rooted paths up to it are transitive. -/
theorem exists_first_nonregular_path [∀ i, Finite (F i)]
    (hd : ∀ i, 3 ≤ ((F (!i)).subgroupOf (F i)).index) :
    ∃ s : ℕ, 0 < s ∧
      (∀ n < s, ∀ v : Vertex F, ∀ p : BasedWalk (graph F) n v,
        p.Nonbacktracking → Regular (A := G) p) ∧
      (∀ v : Vertex F, ∀ n ≤ s, RootPathTransitive (graph F) G v n) ∧
      ∃ v : Vertex F, ∃ p : BasedWalk (graph F) s v,
        p.Nonbacktracking ∧ ¬ RightRegular (A := G) p := by
  classical
  have hex := exists_nonregular_path F hd
  let s := Nat.find hex
  have hshort : ∀ n < s, ∀ v : Vertex F, ∀ p : BasedWalk (graph F) n v,
      p.Nonbacktracking → RightRegular (A := G) p := by
    intro n hn v p hp
    by_contra hbad
    exact Nat.find_min hex hn ⟨v,p,hp,hbad⟩
  have hpos : 0 < s := by
    apply Nat.pos_of_ne_zero
    intro hs
    have hb : ∃ v : Vertex F, ∃ p : BasedWalk (graph F) s v,
        p.Nonbacktracking ∧ ¬ RightRegular (A := G) p := Nat.find_spec hex
    rw [hs] at hb
    obtain ⟨v,p,_,hbad⟩ := hb
    cases p
    exact hbad (rightRegular_zero_of_neighbor_transitive (fun hxy hxz => locally_transitive F hxy hxz) v)
  have ha : GraphAction (graph F) G :=
    ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj h⟩
  refine ⟨s,hpos,?_,?_,Nat.find_spec hex⟩
  · intro n hn v p hp
    exact ⟨(rightRegular_reverse_iff p).mp
      (hshort n hn _ (reverse p) (nonbacktracking_reverse p hp)),
      hshort n hn v p hp⟩
  · intro v n hn
    exact rootPathTransitive_of_short_rightRegular ha s
      (fun n v p hn hp => hshort n hn v p hp) v n hn

/-- A first nonregular path can be chosen through the original marked edge. -/
theorem exists_first_nonregular_path_on_base_edge [∀ i, Finite (F i)]
    (hd : ∀ i, 3 ≤ ((F (!i)).subgroupOf (F i)).index) :
    ∃ n : ℕ,
      (∀ k < n+1, ∀ v : Vertex F, ∀ p : BasedWalk (graph F) k v,
        p.Nonbacktracking → Regular (A := G) p) ∧
      (∀ v : Vertex F, ∀ k ≤ n+1, RootPathTransitive (graph F) G v k) ∧
      ∃ i : Bool, ∃ p : BasedWalk (graph F) (n+1) (base F i),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G) p ∧
        base F false ∈ p.vertices ∧ base F true ∈ p.vertices := by
  obtain ⟨s,hs,hshort,ht,v,p,hp,hbad⟩ := exists_first_nonregular_path F hd
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have hadj : (graph F).Adj v (p.1 : Vertex F) := p.1.property
  obtain ⟨g,hv,hw⟩ := incident_common_translate F hadj.2
  have hv' : g⁻¹ • v = base F v.type := (congrArg (g⁻¹ • ·) hv.symm).trans (inv_smul_smul g _)
  have hw' : g⁻¹ • (p.1 : Vertex F) = base F (p.1 : Vertex F).type := (congrArg (g⁻¹ • ·) hw.symm).trans (inv_smul_smul g _)
  let ha : GraphAction (graph F) G :=
    ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj h⟩
  let q : BasedWalk (graph F) (n+1) (base F v.type) := hv' ▸ p.map (ha.hom g⁻¹)
  have hq : q.Nonbacktracking := (nonbacktracking_cast_base hv' _).mpr
    ((ha.nonbacktracking_map_iff g⁻¹ p).mpr hp)
  have hqv : q.vertices = p.vertices.map (g⁻¹ • ·) :=
    (vertices_cast_base hv' _).trans (BasedWalk.vertices_map _ _)
  have hbadq : ¬ RightRegular (A := G) q := by
    intro hr
    apply hbad
    apply rightRegular_of_conjugate ha q p g _ hr
    rw [hqv,List.map_map]
    simp only [Function.comp_def,smul_inv_smul]
    exact List.map_id _
  have hbase : base F v.type ∈ q.vertices := by
    rw [hqv]
    exact List.mem_map.mpr ⟨v,List.mem_cons_self,hv'⟩
  have hother : base F (p.1 : Vertex F).type ∈ q.vertices := by
    rw [hqv]
    have hm := p.2.toWalk.start_mem_support
    rw [BasedWalk.support_toWalk] at hm
    exact List.mem_map.mpr ⟨p.1,List.mem_cons_of_mem _ hm,hw'⟩
  have hboth (i j : Bool) (hi : base F i ∈ q.vertices) (hj : base F j ∈ q.vertices)
      (hne : i ≠ j) : base F false ∈ q.vertices ∧ base F true ∈ q.vertices := by
    cases i <;> cases j
    · exact (hne rfl).elim
    · exact ⟨hi,hj⟩
    · exact ⟨hj,hi⟩
    · exact (hne rfl).elim
  exact ⟨n,hshort,ht,v.type,q,hq,hbadq,hboth _ _ hbase hother hadj.1⟩
end Subgroup.CosetGeometry.RankTwo
