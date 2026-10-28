module
public import Theory.GroupAction.CubicTree.TrackArcTransport
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# A centered path on the actual reflection line

The track of two adjacent local involutions supplies an even simple path
with a prescribed midpoint and next vertex. The same first involution
reverses every vertex of this path and interchanges its two whole path roots.
This connects literal root/reflection groups to the two-half-path actors.
-/

public section
open SimpleGraph SimpleGraph.Walk SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree Subgroup
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {V X : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

/-- The original two involutions produce a centered path with its literal
half-roots interchanged by the first involution. -/
theorem reflection_centered_path (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ X)
    {a b : V} (hab : Γ.Adj a b) {x y : X}
    (hx : x • a=a) (hy : y • b=b) (hxb : x • b≠b) (hya : y • a≠a)
    (hx2 : x*x=1) (hy2 : y*y=1) (n : ℕ) (hn : 0<n) :
    ∃ (a' b' : V) (p : Γ.Walk a' b'), p.IsPath ∧ p.length=2*n ∧
      p.getVert n=a ∧ p.getVert (n+1)=b ∧
      (∀ k≤2*n, x • p.getVert k=p.getVert (2*n-k)) ∧
      (∀ z∈p.support, z∈Set.range (alternatingVertex (y*x) a b)) ∧
      (pathRoot (X := X) (p.take n)).map (MulAut.conj x).toMonoidHom=pathRoot (p.drop n) ∧
      (pathRoot (X := X) (p.drop n)).map (MulAut.conj x).toMonoidHom=pathRoot (p.take n) := by
  let l := localMoversTrack hΓ hact hab hx hy hxb hya
  let p := (l.arc (-(n : ℤ)) (2*n)).toWalk
  have hp : p.IsPath := isPath_of_nonbacktracking_of_cycle_bound
    (N := 2*n) (fun v c hc => (hΓ c hc).elim) (l.arc (-(n : ℤ)) (2*n))
    (l.arc_nonbacktracking _ _) le_rfl
  have hl : p.length=2*n := BasedWalk.length_toWalk _
  have hv (k : ℕ) (hk : k≤2*n) :
      p.getVert k=alternatingVertex (y*x) a b (-(n : ℤ)+k) := l.arc_getVert _ _ _ hk
  have hmid : p.getVert n=a := by
    rw [hv n (by omega),neg_add_cancel]
    exact localMoversTrack_zero hΓ hact hab hx hy hxb hya
  have hnext : p.getVert (n+1)=b := by
    rw [hv (n+1) (by omega),show -(n : ℤ)+(n+1 : ℕ)=1 by omega]
    exact localMoversTrack_one hΓ hact hab hx hy hxb hya
  have hrev : ∀ k≤2*n, x • p.getVert k=p.getVert (2*n-k) := by
    intro k hk
    rw [hv k hk,hv (2*n-k) (by omega),alternatingVertex_left_reflection hx hy hx2 hy2]
    congr 1
    omega
  refine ⟨_,_,p,hp,hl,hmid,hnext,hrev,?_,(pathRoot_halves_reflection p n hl x hrev).1,
    (pathRoot_halves_reflection p n hl x hrev).2⟩
  intro z hz
  obtain ⟨k,hk,hkl⟩ := mem_support_iff_exists_getVert.mp hz
  exact ⟨-(n : ℤ)+k,(hv k (hl ▸ hkl)).symm.trans hk⟩

end Theory.GroupTheory.WeakBNPair.RegularTree
