module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ReflectionApartment
public import Mathlib.Tactic.IntervalCases

/-!
# Local agreement after changing a tree reflection

An embedded line has a unique simple path with a specified first edge.
This identifies all vertices of a chosen apartment path with the explicit
alternating-reflection coordinates. If one of the two reflections changes
only outside the ball of radius three about its fixed vertex, the old and
new coordinates agree from -3 through 4. The proof uses the two reflection
identities and the distance bounds along the first three edges.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
the shared segment in (14.17), printed p.222. The source uses the opposite
coordinate orientation, giving the same segment from i-4 through i+3.
The literal source application is `ApartmentExchange/SixPathReflectionChange`.
-/

public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

/-- A simple path in an embedded line is determined by its initial oriented edge. -/
theorem path_getVert_eq_line (hΓ : Γ.IsAcyclic) (l : Line Γ)
    {a b : V} (p : Γ.Walk a b) (hp : p.IsPath)
    (hstart : a=l.vertex 0) (hfirst : p.getVert 1=l.vertex 1)
    (hsupport : ∀ v∈p.support, v∈Set.range l.vertex) :
    ∀ k≤p.length, p.getVert k=l.vertex (k : ℤ) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => intro _; simpa only [SimpleGraph.Walk.getVert_zero, Nat.cast_zero] using hstart
  | one => intro _; exact hfirst
  | more k ih₀ ih₁ =>
    intro hk
    have he₀ := ih₀ (by omega : k≤p.length)
    have he₁ := ih₁ (by omega : k+1≤p.length)
    have hstep := p.adj_getVert_succ (by omega : k+1<p.length)
    rw [he₁] at hstep
    have hback : Γ.Adj (l.vertex (↑(k+1))) (l.vertex (↑k)) := by
      simpa only [Nat.cast_add,Nat.cast_one] using (l.adjacent (k : ℤ)).symm
    have hnext : Γ.Adj (l.vertex (↑(k+1))) (l.vertex (↑(k+2))) := by
      simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc,Int.reduceAdd] using
        l.adjacent ((k : ℤ)+1)
    have hne : l.vertex (↑k) ≠ l.vertex (↑(k+2)) := by
      intro he
      have := l.injective he
      omega
    rcases line_noBranching hΓ l _ ⟨((k+1:ℕ):ℤ),rfl⟩ _ ⟨(k:ℤ),rfl⟩ _ ⟨((k+2:ℕ):ℤ),rfl⟩
      _ (hsupport _ (p.getVert_mem_support _)) hback hnext hstep hne with he | he
    · have := hp.getVert_injOn hk (by omega : k≤p.length) (he.trans he₀.symm)
      omega
    · exact he

/-- Agreement on the radius-three ball preserves the eight central line vertices. -/
theorem alternatingVertex_eq_of_agree_three_ball
    (hact : GraphAction Γ X) {a b : V} (hab : Γ.Adj a b)
    {x x' y : X} (hx : x • a=a) (hx' : x' • a=a) (hy : y • b=b)
    (hx2 : x*x=1) (hx2' : x'*x'=1) (hy2 : y*y=1)
    (hagree : ∀ v, Γ.edist a v ≤ (3 : ℕ∞) → x' • v=x • v)
    (j : ℤ) (hj : -3 ≤ j ∧ j ≤ 4) :
    alternatingVertex (y*x') a b j = alternatingVertex (y*x) a b j := by
  let v := alternatingVertex (y*x) a b
  let w := alternatingVertex (y*x') a b
  have hl (j : ℤ) : x • v j=v (-j) :=
    alternatingVertex_left_reflection hx hy hx2 hy2 j
  have hr (j : ℤ) : y • v j=v (2-j) :=
    alternatingVertex_right_reflection hx hy hx2 hy2 j
  have hl' (j : ℤ) : x' • w j=w (-j) :=
    alternatingVertex_left_reflection hx' hy hx2' hy2 j
  have hr' (j : ℤ) : y • w j=w (2-j) :=
    alternatingVertex_right_reflection hx' hy hx2' hy2 j
  have hb : v 1=b := by simp [v,alternatingVertex]
  have adj (j : ℤ) : Γ.Adj (v j) (v (j+1)) := alternatingVertex_adj hact hab hx hy j
  have hd1 : Γ.edist a (v 1) ≤ (1 : ℕ∞) := by
    rw [hb]
    exact (edist_eq_one_iff_adj.mpr hab).le
  have hd2 : Γ.edist a (v 2) ≤ (2 : ℕ∞) := by
    calc
      _ ≤ Γ.edist a (v 1) + Γ.edist (v 1) (v 2) := Γ.edist_triangle
      _ ≤ 1+1 := add_le_add hd1 (edist_eq_one_iff_adj.mpr (adj 1)).le
      _ = 2 := by norm_num
  have hd3 : Γ.edist a (v 3) ≤ (3 : ℕ∞) := by
    calc
      _ ≤ Γ.edist a (v 2) + Γ.edist (v 2) (v 3) := Γ.edist_triangle
      _ ≤ 2+1 := add_le_add hd2 (edist_eq_one_iff_adj.mpr (adj 2)).le
      _ = 3 := by norm_num
  have e0 : w 0=v 0 := by simp [v,w,alternatingVertex]
  have e1 : w 1=v 1 := by simp [v,w,alternatingVertex]
  have en1 : w (-1)=v (-1) := by
    calc
      _ = x' • w 1 := (hl' 1).symm
      _ = x' • v 1 := congrArg (x' • ·) e1
      _ = x • v 1 := hagree _ (hd1.trans (by norm_num))
      _ = _ := hl 1
  have e2 : w 2=v 2 := by
    calc
      _ = y • w 0 := (hr' 0).symm
      _ = y • v 0 := congrArg (y • ·) e0
      _ = _ := hr 0
  have en2 : w (-2)=v (-2) := by
    calc
      _ = x' • w 2 := (hl' 2).symm
      _ = x' • v 2 := congrArg (x' • ·) e2
      _ = x • v 2 := hagree _ (hd2.trans (by norm_num))
      _ = _ := hl 2
  have e3 : w 3=v 3 := by
    calc
      _ = y • w (-1) := (hr' (-1)).symm
      _ = y • v (-1) := congrArg (y • ·) en1
      _ = _ := hr (-1)
  have en3 : w (-3)=v (-3) := by
    calc
      _ = x' • w 3 := (hl' 3).symm
      _ = x' • v 3 := congrArg (x' • ·) e3
      _ = x • v 3 := hagree _ hd3
      _ = _ := hl 3
  have e4 : w 4=v 4 := by
    calc
      _ = y • w (-2) := (hr' (-2)).symm
      _ = y • v (-2) := congrArg (y • ·) en2
      _ = _ := hr (-2)
  change w j=v j
  obtain ⟨hlo,hhi⟩ := hj
  interval_cases j <;> assumption

end Theory.GroupTheory.WeakBNPair.RegularTree
