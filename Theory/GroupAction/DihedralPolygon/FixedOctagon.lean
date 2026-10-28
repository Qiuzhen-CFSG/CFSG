module

public import Theory.GroupAction.DihedralPolygon
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortFix
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.QuadrangleRecognition

/-!
# Closing a dihedral arc in a thin fixed graph

In a bipartite graph of girth at least sixteen and diameter at most eight,
the endpoints of a nine-edge arc admit a geodesic of length at most seven.
If a fixed-point predicate is preserved along these short geodesics and
has precisely the two expected neighbors on the dihedral arc, that
geodesic forces the arc to close after sixteen edges. Thus the eighth
rotation power fixes the initial edge.

The torus of the nonbinary Ree amalgam supplies the fixed-point predicate.
This is a direct specialized apartment argument for the small-completion
step in Aschbacher–Smith F.4.10 and F.4.16, printed pp.279,282.
The native torus calculations supply the two-neighbor and fixed-path inputs
in the Ree extension-completion consumer.
-/

@[expose] public section

namespace SimpleGraph.OctagonApartment
variable {V : Type*} {Γ : SimpleGraph V}

private theorem walk_index (a : ℕ → V) (Q : V → Prop)
    (hn : ∀ i, 0  <  i → i  <  16 → ∀ v, Γ.Adj (a i) v → Q v →
      v=a (i - 1) ∨ v=a (i + 1))
    {x y : V} (p : Γ.Walk x y) (hp : ∀ v∈p.support,Q v)
    (i : ℕ) (hx : x=a i) (hi : p.length  <  i) (hi' : i + p.length ≤ 16) :
    ∃ j,i - p.length ≤ j ∧ j ≤ i + p.length ∧ y=a j := by
  induction p generalizing i with
  | nil => exact ⟨i,by simp,by simp,hx⟩
  | @cons x z y h p ih =>
    have hzQ : Q z := hp z (by simp)
    have hpy : ∀v∈p.support,Q v := fun v hv => hp v (by simp [hv])
    have hz := hn i (by simp only [Walk.length_cons] at hi; omega)
      (by simp only [Walk.length_cons] at hi'; omega) z (hx ▸ h) hzQ
    rcases hz with hz | hz
    · obtain ⟨j,hj,hj',he⟩ := ih hpy (i - 1) hz
        (by simp only [Walk.length_cons] at hi; omega)
        (by simp only [Walk.length_cons] at hi'; omega)
      refine ⟨j,?_,?_,he⟩  <;> simp only [Walk.length_cons]  <;> omega
    · obtain ⟨j,hj,hj',he⟩ := ih hpy (i + 1) hz
        (by simp only [Walk.length_cons] at hi; omega)
        (by simp only [Walk.length_cons] at hi'; omega)
      refine ⟨j,?_,?_,he⟩  <;> simp only [Walk.length_cons]  <;> omega

/-- A short fixed path closes a locally thin sixteen-arc. -/
theorem sequence_closes_of_short_fixed_walk (a : ℕ → V) (Q : V → Prop)
    (hQ : ∀i,Q (a i)) (hadj : ∀i,Γ.Adj (a i) (a (i + 1)))
    (hinj : Set.InjOn a (Set.Icc 0 15))
    (hn : ∀ i, 0  <  i → i  ≤  16 → ∀ v, Γ.Adj (a i) v → Q v →
      v=a (i - 1) ∨ v=a (i + 1))
    (p : Γ.Walk (a 9) (a 0)) (hp : ∀v∈p.support,Q v) (hlen : p.length ≤ 7) :
    a 16=a 0 ∧ a 17=a 1 := by
  obtain ⟨j,hj,hj',he⟩ := walk_index a Q (fun i hi hi' => hn i hi (by omega))
    p hp 9 rfl (by omega) (by omega)
  have hj12 : j=16 := by
    by_contra h
    have hh := hinj (x₁ := 0) (x₂ := j) (by simp) (by simp; omega) he
    omega
  have he12 : a 16=a 0 := by simpa [hj12] using he.symm
  refine ⟨he12,?_⟩
  have hh := hn 16 (by decide) le_rfl (a 1) (he12.symm ▸ hadj 0) (hQ 1)
  rcases hh with h | h
  · have hh := hinj (x₁ := 1) (x₂ := 15) (by simp) (by simp) h
    omega
  · exact h.symm
end SimpleGraph.OctagonApartment

namespace SimpleGraph.OctagonApartment
open PathTransitivePolygon
variable {V A : Type*} [Group A] [MulAction A V] {Γ : SimpleGraph V}

theorem short_geodesic_fixed (hg : ∀v(p : Γ.Walk v v),p.IsCycle → 16≤p.length)
    (act : GraphAction Γ A) {x y : V} (p : Γ.Walk x y)
    (hp : p.IsPath) (hl : p.length≤7) (a : A) (hx : a • x=x) (hy : a • y=y) :
    ∀v∈p.support,a • v=v := by
  let f : Γ ≃g Γ := { toEquiv := MulAction.toPerm a, map_rel_iff' := act.adj_iff a }
  have hfix := BasedWalk.fixes_short_walk (N := 15)
    (fun v q hq => (show 15 < 16 by decide).trans_le (hg v q hq))
    (BasedWalk.ofWalk p) (BasedWalk.nonbacktracking_ofWalk_of_isPath p hp)
    (by omega) f hx (by
      change a • (BasedWalk.ofWalk p).endpoint=(BasedWalk.ofWalk p).endpoint
      rw [BasedWalk.endpoint_ofWalk]
      exact hy)
  intro v hv
  have hh := hfix v (by simpa only [BasedWalk.vertices_ofWalk] using hv)
  change a • v=v at hh
  exact hh

/-- A fifteen-edge locally nonbacktracking sequence is injective below girth sixteen. -/
theorem sequence_injective_of_girth
    (hg : ∀v(p : Γ.Walk v v),p.IsCycle → 16≤p.length)
    (a : ℕ → V) (hadj : ∀i,Γ.Adj (a i) (a (i+1)))
    (hnb : ∀i,a i≠a (i+2)) : Set.InjOn a (Set.Icc 0 15) := by
  have convertNB {x y : V} (p : Γ.Walk x y) (hp : p.Nonbacktracking) :
      (BasedWalk.ofWalk p).Nonbacktracking := by
    induction p with
    | nil => trivial
    | @cons x y z h p ih =>
      cases p with
      | nil => trivial
      | @cons y t z h' q =>
        refine ⟨?_,ih hp.tail_cons⟩
        have hh := hp 0 (by simp)
        simpa only [Walk.getVert_zero,Walk.getVert_cons_succ,BasedWalk.ofWalk] using hh.symm
  have walkNB (i n : ℕ) := convertNB (chainWalk a hadj i n)
    (chainWalk_nonbacktracking a hadj hnb i n)
  let p := chainWalk a hadj 0 15
  have hp : p.IsPath := isPath_of_nonbacktracking_of_cycle_bound
    (N := 15) (fun v q hq => (show 15 < 16 by decide).trans_le (hg v q hq))
    (BasedWalk.ofWalk p) (walkNB 0 15) (by simp [p])
  intro i hi j hj he
  apply hp.getVert_injOn (by simpa [p] using hi.2) (by simpa [p] using hj.2)
  simpa only [p,getVert_chainWalk a hadj 0 15 i hi.2,
    getVert_chainWalk a hadj 0 15 j hj.2,Nat.zero_add] using he
end SimpleGraph.OctagonApartment

namespace GroupAction.DihedralPolygon.OctagonApartment
open SimpleGraph SimpleGraph.OctagonApartment
variable {G V : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable (D : BipartiteAction G Γ) (s t : G) (x l : V)
variable (hs : s^2=1) (ht : t^2=1) (hsx : s • x=x) (htl : t • l=l)

include D hs ht hsx htl in
theorem fixed_edge_sequence_closes (hxl : Γ.Adj x l)
    (hsl : s • l≠l) (htx : t • x≠x)
    (hconn : Γ.Connected) (hdiam : ∀v w,Γ.dist v w≤8)
    (hg : ∀v(p : Γ.Walk v v),p.IsCycle → 16≤p.length)
    (Q : V → Prop) (hQx : Q x) (hQl : Q l)
    (hQs : ∀v,Q (s • v) ↔ Q v) (hQt : ∀v,Q (t • v) ↔ Q v)
    (hNx : ∀v,Γ.Adj x v → Q v → v=l ∨ v=s • l)
    (hNl : ∀v,Γ.Adj l v → Q v → v=x ∨ v=t • x)
    (hQpath : ∀ {v w} (p : Γ.Walk v w),p.IsPath → p.length≤7 →
      Q v → Q w → ∀u∈p.support,Q u) :
    (t*s)^8 • x=x ∧ (t*s)^8 • l=l := by
  let r := t*s
  let a := edgeVertex s t x l
  have hss : s*s=1 := by simpa only [pow_two] using hs
  have htt : t*t=1 := by simpa only [pow_two] using ht
  have hQpow (n : ℕ) (v : V) : Q (r^n • v) ↔ Q v := by
    induction n generalizing v with
    | zero => simp
    | succ n ih => simp only [pow_succ,mul_smul,ih,r,hQt,hQs]
  have hQa (i : ℕ) : Q (a i) := by
    change Q (r^(i/2) • (if i%2=0 then x else l))
    apply (hQpow _ _).mpr
    split_ifs <;> assumption
  have hadj (i : ℕ) : Γ.Adj (a i) (a (i+1)) := by
    by_cases hi : i%2=0
    · have hj : (i+1)%2≠0 := by omega
      have hd : (i+1)/2=i/2 := by omega
      simpa only [a,edgeVertex,if_pos hi,if_neg hj,hd] using D.smul_adj (r^(i/2)) hxl
    · have hj : (i+1)%2=0 := by omega
      have hd : (i+1)/2=i/2+1 := by omega
      have hh : Γ.Adj l (r • x) := by
        simpa only [r,mul_smul,hsx,htl] using D.smul_adj t hxl.symm
      simpa only [a,edgeVertex,if_neg hi,if_pos hj,hd,pow_succ,mul_smul,r] using
        D.smul_adj (r^(i/2)) hh
  have hnb (i : ℕ) : a i≠a (i+2) := by
    have hrx : r • x≠x := by simpa only [r,mul_smul,hsx] using htx
    have hrl : r • l≠l := by
      intro he
      have hh := congrArg (t • ·) he
      exact hsl (by simpa only [r,mul_smul,←mul_smul t t,htt,one_smul,htl] using hh)
    have hd : (i+2)/2=i/2+1 := by omega
    have hm : (i+2)%2=i%2 := by omega
    dsimp [a,edgeVertex]
    rw [hd,hm,pow_succ,mul_smul]
    intro he
    have hh := MulAction.injective (r^(i/2)) he
    split_ifs at hh <;> first | exact hrx hh.symm | exact hrl hh.symm
  have hn (i : ℕ) (hi : 0 < i) (_ : i≤16) (v : V)
      (hv : Γ.Adj (a i) v) (hQv : Q v) : v=a (i-1) ∨ v=a (i+1) := by
    let k := i/2
    have hundo : Q ((r^k)⁻¹ • v) := by
      apply (hQpow k _).mp
      simpa only [smul_inv_smul] using hQv
    have hv' := D.smul_adj (r^k)⁻¹ hv
    by_cases hi2 : i%2=0
    · simp only [a,edgeVertex,if_pos hi2,r,k,inv_smul_smul] at hv'
      rcases hNx _ hv' hundo with he | he
      · right
        have hh := congrArg (r^k • ·) he
        have hd : (i+1)/2=k := by dsimp [k]; omega
        have hm : (i+1)%2≠0 := by omega
        simpa only [r,k,smul_inv_smul,a,edgeVertex,hd,if_neg hm] using hh
      · left
        have hh := congrArg (r^k • ·) he
        rw [smul_inv_smul] at hh
        have hk : 0 < k := by dsimp [k]; omega
        have hks : k=(k-1)+1 := by omega
        have hd : (i-1)/2=k-1 := by dsimp [k]; omega
        have hm : (i-1)%2≠0 := by omega
        rw [hh]
        simp only [a,edgeVertex,hd,if_neg hm]
        nth_rw 1 [hks]
        simp only [pow_succ,mul_smul,r,←mul_smul s s,hss,one_smul,htl]
    · simp only [a,edgeVertex,if_neg hi2,r,k,inv_smul_smul] at hv'
      rcases hNl _ hv' hundo with he | he
      · left
        have hh := congrArg (r^k • ·) he
        have hd : (i-1)/2=k := by dsimp [k]; omega
        have hm : (i-1)%2=0 := by omega
        simpa only [r,k,smul_inv_smul,a,edgeVertex,hd,if_pos hm] using hh
      · right
        have hh := congrArg (r^k • ·) he
        have hd : (i+1)/2=k+1 := by dsimp [k]; omega
        have hm : (i+1)%2=0 := by omega
        simpa only [r,k,smul_inv_smul,a,edgeVertex,hd,if_pos hm,pow_succ,mul_smul,hsx] using hh
  obtain ⟨p,hp,hl⟩ := hconn.exists_path_of_dist (a 9) (a 0)
  have hlen : p.length≤7 := by
    have hd := hdiam (a 9) (a 0)
    have hne : D.color (a 9)≠D.color (a 0) := by
      simpa only [a,edgeVertex,show 9/2=4 from rfl,show 9%2=1 from rfl,
        show 0/2=0 from rfl,show 0%2=0 from rfl,ite_false,ite_true,Nat.one_ne_zero,
        pow_zero,one_smul,D.smul_color] using (D.adjacent_color hxl).symm
    have hnE : ¬Even p.length := by
      intro he
      exact hne ((PathTransitivePolygon.QuadrangleRecognition.even_length_iff
        D.color D.adjacent_color p).mp he)
    have hne6 : p.length≠8 := by rintro h; exact hnE (h ▸ by decide)
    omega
  have hh := sequence_closes_of_short_fixed_walk a Q hQa hadj
    (sequence_injective_of_girth hg a hadj hnb) hn p (hQpath p hp hlen (hQa 9) (hQa 0)) hlen
  simpa only [a,edgeVertex,show 16/2=8 from rfl,show 16%2=0 from rfl,
    show 17/2=8 from rfl,show 17%2=1 from rfl,show 0/2=0 from rfl,show 0%2=0 from rfl,
    show 1/2=0 from rfl,show 1%2=1 from rfl,ite_true,ite_false,Nat.one_ne_zero,pow_zero,one_smul] using hh
end GroupAction.DihedralPolygon.OctagonApartment
