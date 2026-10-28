module
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount
public import Theory.GroupAction.RankTwoCosetGeometry.PathKernelTransport
public import Theory.GroupAction.CubicTree.ArcReversal
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Ring

/-!
# Seven-path transitivity from one odd fixer

In a bipartite coset graph of valences `q₀ + 1` and `q₁ + 1`, there are
`q₀³ q₁³` nonbacktracking seven-paths through a fixed first edge. An edge
two-subgroup of that order acts freely on a path with odd pointwise fixer,
so its orbit fills the edge-rooted path set. Local transitivity then gives
rooted transitivity. Reversing the odd-length witness covers the other
vertex type, and conjugation transports the odd fixer to every seven-path.

Source: DGS, *Groups and Graphs* (1985), (10.10), printed p.164.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
namespace Subgroup.CosetGeometry.RankTwo

private def edgePathsEquiv {V : Type*} (Γ : SimpleGraph V) (n : ℕ)
    (a : V) (b : Γ.neighborSet a) :
    {p : BasedWalk Γ (n+1) a // p.Nonbacktracking ∧ p.1 = b} ≃
      BasedWalk.Forward Γ n a b :=
  (show {p : BasedWalk Γ (n+1) a // p.Nonbacktracking ∧ p.1 = b} ≃
      {p : BasedWalk Γ n b // Avoids Γ a p} from {
    toFun := by
      rintro ⟨⟨c,p⟩,hp,hc⟩
      change c = b at hc
      subst c
      exact ⟨p,by cases n <;> exact hp⟩
    invFun := fun p => ⟨⟨b,p.val⟩,by cases n <;> exact p.property,rfl⟩
    left_inv := by rintro ⟨⟨c,p⟩,hp,hc⟩; change c = b at hc; subst c; rfl
    right_inv := by intro p; rfl }).trans (forwardEquiv Γ n a b).symm

private theorem first_smul {G : Type*} [Group G] (F : Bool → Subgroup G)
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) (n+1) a)
    (g : stabilizer F a) : ((actPath F g p).1 : Vertex F) = (g : G) • (p.1 : Vertex F) := by
  have hh := congrArg (fun l : List (Vertex F) => l.tail.head?) (vertices_actPath F g p)
  simpa only [BasedWalk.vertices, List.tail_cons, List.map_cons, head_vertices,
    List.head?_map, Option.map_some, Option.some.injEq] using hh

private theorem edge_transitive_of_odd {G : Type*} [Group G]
    (F : Bool → Subgroup G) (qv : Bool → ℕ) (hpos : ∀ i, 0 < qv i) (hval : ∀ v : Vertex F,
      Nat.card ((graph F).neighborSet v) = qv v.type+1)
    {a : Vertex F} (b : (graph F).neighborSet a)
    (T : Subgroup G) (hT : T ≤ stabilizer F a ⊓ stabilizer F b)
    (hTc : Nat.card T = qv false^3 * qv true^3) (hTp : IsPGroup 2 T)
    (p : BasedWalk (graph F) 7 a) (hp : p.Nonbacktracking)
    (hpb : p.1 = b) (hodd : Odd (Nat.card (pathStabilizer F p))) :
    ∀ q : BasedWalk (graph F) 7 a, q.Nonbacktracking →
      q.1 = b → ∃ g ∈ T, p.vertices.map (g • ·) = q.vertices := by
  classical
  let : MulAction (stabilizer F a) (BasedWalk (graph F) 7 a) := pathAction F 7 a
  intro q hq hqb
  let Y := {p : BasedWalk (graph F) 7 a // p.Nonbacktracking ∧ p.1 = b}
  let : ∀ v : Vertex F, Finite ((graph F).neighborSet v) :=
    fun v => Nat.finite_of_card_ne_zero (by rw [hval]; exact Nat.succ_ne_zero _)
  have hflip : ∀ {v w : Vertex F}, (graph F).Adj v w → w.type = !v.type := by
    intro v w hvw
    have hn := hvw.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have hY : Nat.card Y = qv false^3 * qv true^3 := by
    rw [Nat.card_congr (edgePathsEquiv (graph F) 6 a b),
      card_forward (graph F) (fun v => v.type) (fun i => qv i+1) hflip hval 6 a b b.property]
    cases (b : Vertex F).type <;>
      simp only [BasedWalk.forwardCount, Bool.not_false, Bool.not_true,
        Nat.add_sub_cancel, mul_one] <;>
      ring
  let : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY]; exact ne_of_gt (mul_pos (pow_pos (hpos false) _) (pow_pos (hpos true) _)))
  let : Finite T := Nat.finite_of_card_ne_zero (by rw [hTc]; exact ne_of_gt (mul_pos (pow_pos (hpos false) _) (pow_pos (hpos true) _)))
  let : Finite (pathStabilizer F p) := Nat.finite_of_card_ne_zero (by
    have hh := hodd; intro hz; rw [hz] at hh; exact (by decide : ¬Odd (0:ℕ)) hh)
  let j : T →* stabilizer F a := inclusion (hT.trans inf_le_left)
  let f : T → Y := fun x => ⟨j x • p,
    (nonbacktracking_smul_path F (j x) p).mpr hp,by
      apply Subtype.ext
      change ((actPath F (j x) p).1 : Vertex F) = b
      rw [first_smul,hpb]
      exact (hT x.property).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hs : j x • p = j y • p := congrArg Subtype.val hxy
    have hz : ((j x)⁻¹ * j y) • p = p := by
      rw [mul_smul,←hs,inv_smul_smul]
    have hfix : ((x : G)⁻¹ * y) ∈ pathStabilizer F p :=
      (mem_pathStabilizer_iff F p ((j x)⁻¹ * j y)).mpr hz
    obtain ⟨k,hk⟩ := hTp (x⁻¹*y)
    have hd : orderOf ((x : G)⁻¹*y) ∣ 2^k := by
      change orderOf ((x⁻¹*y : T) : G) ∣ 2^k
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hk
    have ho : orderOf ((x : G)⁻¹*y) ∣ Nat.card (pathStabilizer F p) := by
      simpa only [Subgroup.orderOf_mk] using _root_.orderOf_dvd_natCard
        (⟨_,hfix⟩ : pathStabilizer F p)
    apply Subtype.ext
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_right.pow_right k) ho hd))
  obtain ⟨x,hx⟩ := (hf.bijective_of_nat_card_le (by omega : Nat.card Y ≤ Nat.card T)).surjective ⟨q,hq,hqb⟩
  exact ⟨x,x.property,(vertices_smul_path F (j x) p).symm.trans
    (congrArg BasedWalk.vertices (congrArg Subtype.val hx))⟩

/-- One odd seven-path fixer and the edge-core order force transitivity
on all nonbacktracking seven-paths with the same initial vertex. -/
theorem seven_path_transitive_of_odd_witness {G : Type*} [Group G]
    (F : Bool → Subgroup G) (qv : Bool → ℕ) (hpos : ∀ i, 0 < qv i)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = qv v.type+1)
    (hcard : ∀ {a b : Vertex F}, (graph F).Adj a b →
      Nat.card ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) = qv false^3 * qv true^3)
    {a : Vertex F} (p : BasedWalk (graph F) 7 a) (hp : p.Nonbacktracking)
    (hodd : Odd (Nat.card (pathStabilizer F p))) :
    RootPathTransitive (graph F) G a 7 := by
  let : MulAction (stabilizer F a) (BasedWalk (graph F) 7 a) := pathAction F 7 a
  have hreach : ∀ r : BasedWalk (graph F) 7 a, r.Nonbacktracking →
      ∃ g : stabilizer F a, g • p = r := by
    intro r hr
    obtain ⟨g,hga,hg⟩ := locally_transitive F r.1.property p.1.property
    let g' : stabilizer F a := ⟨g,hga⟩
    let r' := g' • r
    have hr' : r'.Nonbacktracking := (nonbacktracking_smul_path F g' r).mpr hr
    have hfirst : r'.1 = p.1 := Subtype.ext ((first_smul F r g').trans hg)
    let E := stabilizer F a ⊓ stabilizer F (p.1 : Vertex F)
    obtain ⟨t,ht,htr⟩ := edge_transitive_of_odd F qv hpos hval p.1
      (E.pCoreIn 2) (E.pCoreIn_le 2) (hcard p.1.property)
      (isPGroup_pCoreIn 2 E) p hp rfl hodd r' hr' hfirst
    let t' : stabilizer F a := ⟨t,((E.pCoreIn_le 2) ht).1⟩
    have htp : t' • p = r' := BasedWalk.vertices_injective 7 a
      ((vertices_smul_path F t' p).trans htr)
    refine ⟨g'⁻¹*t',?_⟩
    rw [mul_smul,htp]
    exact inv_smul_smul g' r
  intro r s hr hs
  obtain ⟨u,hu⟩ := hreach r hr
  obtain ⟨v,hv⟩ := hreach s hs
  have he : (v*u⁻¹) • r = s := by
    rw [mul_smul,←hu,inv_smul_smul,hv]
  exact ⟨(v*u⁻¹ : stabilizer F a), (v*u⁻¹).property,
    (vertices_smul_path F (v*u⁻¹) r).symm.trans (congrArg BasedWalk.vertices he)⟩

private theorem exists_odd_path_of_same_type {G : Type*} [Group G]
    (F : Bool → Subgroup G) {n : ℕ} {a b : Vertex F}
    (p : BasedWalk (graph F) n a) (hp : p.Nonbacktracking)
    (ho : Odd (Nat.card (pathStabilizer F p))) (ht : a.type = b.type) :
    ∃ r : BasedWalk (graph F) n b,
      r.Nonbacktracking ∧ Odd (Nat.card (pathStabilizer F r)) := by
  obtain ⟨g,hg⟩ := (same_orbit_iff F a b).mpr ht
  let r := BasedWalk.rebase hg (p.map (translationGraphIso F g).toHom)
  have hv : p.vertices.map (g • ·) = r.vertices :=
    ((BasedWalk.vertices_rebase hg _).trans
      (BasedWalk.vertices_map (translationGraphIso F g).toHom p)).symm
  refine ⟨r,?_,?_⟩
  · exact (BasedWalk.nonbacktracking_rebase _ _).mpr
      ((BasedWalk.nonbacktracking_map_iff (translationGraphIso F g).toHom
        (fun v => (translationGraphIso F g).mapNeighborSet v |>.injective) p).mpr hp)
  · rw [←pathStabilizer_map_conj_of_vertices F p r g hv,
      card_map_of_injective (MulAut.conj g).injective]
    exact ho

/-- Reversal of an odd-length witness supplies the second vertex orbit.
Both rooted transitivity and odd seven-path fixers follow everywhere. -/
theorem seven_path_geometry_of_odd_witness {G : Type*} [Group G]
    (F : Bool → Subgroup G) (qv : Bool → ℕ) (hpos : ∀ i, 0 < qv i)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = qv v.type+1)
    (hcard : ∀ {a b : Vertex F}, (graph F).Adj a b →
      Nat.card ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) = qv false^3 * qv true^3)
    {a : Vertex F} (p : BasedWalk (graph F) 7 a) (hp : p.Nonbacktracking)
    (hodd : Odd (Nat.card (pathStabilizer F p))) :
    (∀ v : Vertex F, RootPathTransitive (graph F) G v 7) ∧
    (∀ {v : Vertex F} (r : BasedWalk (graph F) 7 v), r.Nonbacktracking →
      Odd (Nat.card (pathStabilizer F r))) := by
  have hends : a.type ≠ p.endpoint.type := by
    intro he
    have hh := (even_walk_iff F p.toWalk).mpr he
    rw [BasedWalk.length_toWalk] at hh
    exact (by decide : ¬ Even (7:ℕ)) hh
  have hrev : pathStabilizer F (Theory.GroupAction.CubicTree.reverse p) =
      pathStabilizer F p := by
    ext g
    simp only [pathStabilizer, mem_mk,
      Theory.GroupAction.CubicTree.vertices_reverse, List.mem_reverse]
  have hex : ∀ v : Vertex F, ∃ r : BasedWalk (graph F) 7 v,
      r.Nonbacktracking ∧ Odd (Nat.card (pathStabilizer F r)) := by
    intro v
    by_cases ht : a.type = v.type
    · exact exists_odd_path_of_same_type F p hp hodd ht
    · have ht' : p.endpoint.type = v.type := by
        cases ha : a.type <;> cases hb : p.endpoint.type <;> cases hv : v.type <;>
          simp_all
      exact exists_odd_path_of_same_type F (Theory.GroupAction.CubicTree.reverse p)
        (Theory.GroupAction.CubicTree.nonbacktracking_reverse p hp) (hrev ▸ hodd) ht'
  have htrans : ∀ v : Vertex F, RootPathTransitive (graph F) G v 7 := by
    intro v
    obtain ⟨r,hr,ho⟩ := hex v
    exact seven_path_transitive_of_odd_witness F qv hpos hval hcard r hr ho
  refine ⟨htrans,?_⟩
  intro v r hr
  obtain ⟨s,hs,ho⟩ := hex v
  obtain ⟨g,_,hg⟩ := htrans v s r hs hr
  rw [←pathStabilizer_map_conj_of_vertices F s r g hg,
    card_map_of_injective (MulAut.conj g).injective]
  exact ho

/-- A longer nonbacktracking path has fixer contained in its seven-prefix
fixer; hence oddness of seven-path fixers propagates to every longer path. -/
theorem long_path_fixer_odd_of_seven {G : Type*} [Group G]
    (F : Bool → Subgroup G)
    (hodd : ∀ {v : Vertex F} (r : BasedWalk (graph F) 7 v), r.Nonbacktracking →
      Odd (Nat.card (pathStabilizer F r)))
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a)
    (hp : p.Nonbacktracking) (hn : 7 ≤ n) :
    Odd (Nat.card (pathStabilizer F p)) := by
  let r := p.take 7 hn
  have ho := hodd r (nonbacktracking_take hn p hp)
  let : Finite (pathStabilizer F r) := Nat.finite_of_card_ne_zero (by
    intro hz
    rw [hz] at ho
    exact (by decide : ¬ Odd (0:ℕ)) ho)
  apply Odd.of_dvd_nat ho
  apply card_dvd_of_le
  intro g hg z hz
  apply hg z
  rw [BasedWalk.vertices_take] at hz
  exact List.mem_of_mem_take hz

end Subgroup.CosetGeometry.RankTwo
