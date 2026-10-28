module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ChainSeparation
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# Two-subgroups fixing branching tree paths

Two simple paths that start at the same vertex with different first edges
form a simple path after reversing the first one. If that joined path has
at least s edges and every s-path fixer has odd order, a two-subgroup
fixing both original paths is trivial.

For two long-path radicals, apply this argument after removing the first
edge of each path. If a conjugating element aligns their first vertices
but separates their second vertices, the conjugate radical and the other
radical have trivial intersection. The map is literally conjugation by
that element; no quotient action or global kernel is used.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
the branching-path contradiction in (14.17), printed p.222. The original
universal-tree application is in ApartmentExchange/SixPathRootSeparation.
-/

public section
open SimpleGraph SimpleGraph.Walk
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

private theorem diverging_path (ht : Γ.IsTree) {a b c : V}
    (p : Γ.Walk a b) (q : Γ.Walk a c) (hp : p.IsPath) (hq : q.IsPath)
    (hne : p.snd ≠ q.snd) : (p.reverse.append q).IsPath := by
  obtain ⟨v,l,u,w,he₁,he₂,hu⟩ := tree_tripod ht p q hp hq
  cases l with
  | nil =>
    simp only [nil_append] at he₁ he₂
    simpa only [he₁,he₂] using hu
  | cons h l =>
    exfalso
    apply hne
    simp only [he₁,he₂,cons_append,SimpleGraph.Walk.snd,getVert_cons_succ,getVert_zero]

/-- Odd s-path fixers exclude a nontrivial two-subgroup fixing two branches
whose total length is at least s. -/
theorem two_subgroup_eq_bot_of_diverging_paths (ht : Γ.IsTree)
    (s : ℕ)
    (hodd : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=s →
      Odd (Nat.card (pathFixer (X := X) p)))
    {a b c : V} (p : Γ.Walk a b) (q : Γ.Walk a c)
    (hp : p.IsPath) (hq : q.IsPath) (hne : p.snd ≠ q.snd)
    (hlen : s ≤ p.length+q.length) (H : Subgroup X) (hH : IsPGroup 2 H)
    (hHp : H ≤ pathFixer p) (hHq : H ≤ pathFixer q) : H=⊥ := by
  let w := p.reverse.append q
  have hw : w.IsPath := diverging_path ht p q hp hq hne
  have hws : (w.take s).length=s := by
    rw [take_length]
    exact min_eq_left (by simpa only [w,length_append,length_reverse] using hlen)
  have ho := hodd (w.take s) (hw.take s) hws
  apply le_bot_iff.mp
  intro x hx
  have hfix : x∈pathFixer (X := X) (w.take s) := by
    apply (mem_pathFixer_support _ _).mpr
    intro v hv
    have hvw : v∈w.support := List.mem_of_mem_take (by
      simpa only [support_take] using hv)
    have hv' : v∈p.support ∨ v∈q.support := by
      rcases List.mem_append.mp (show v∈p.reverse.support ++ q.support.tail by
        simpa only [w,support_append] using hvw) with hh | hh
      · exact Or.inl (by simpa only [support_reverse,List.mem_reverse] using hh)
      · exact Or.inr (List.mem_of_mem_tail hh)
    rcases hv' with hv | hv
    · exact (mem_pathFixer_support p x).mp (hHp hx) v hv
    · exact (mem_pathFixer_support q x).mp (hHq hx) v hv
  obtain ⟨k,hk⟩ := hH ⟨x,hx⟩
  have hp : orderOf x ∣ 2^k := by
    simpa only [Subgroup.orderOf_mk] using orderOf_dvd_of_pow_eq_one hk
  have hd : orderOf x ∣ Nat.card (pathFixer (X := X) (w.take s)) := by
    simpa only [Subgroup.orderOf_mk] using
      orderOf_dvd_natCard (⟨x,hfix⟩ : pathFixer (X := X) (w.take s))
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (ho.coprime_two_right.pow_right k) hd hp)

/-- A conjugate of one path radical has trivial intersection with another
when their translated tails branch and together have at least s edges. -/
theorem conjugate_pathRoot_inf_eq_bot_of_branch (ht : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (s : ℕ)
    (hodd : ∀ {a b} (p : Γ.Walk a b), p.IsPath → p.length=s →
      Odd (Nat.card (pathFixer (X := X) p)))
    {a b c d : V} (p : Γ.Walk a b) (q : Γ.Walk c d)
    (hp : p.IsPath) (hq : q.IsPath) (hp0 : 0<p.length) (hq0 : 0<q.length)
    (hlen : s ≤ (p.length-1)+(q.length-1)) (z : X)
    (hz1 : z • p.getVert 1=q.getVert 1)
    (hz2 : z • p.getVert 2≠q.getVert 2) :
    (pathRoot (X := X) p).map (MulAut.conj z).toMonoidHom ⊓ pathRoot q=⊥ := by
  let f : Γ →g Γ := ⟨(z • ·),hact z⟩
  let P := ((p.map f).drop 1).copy
    (show (p.map f).getVert 1=q.getVert 1 from (getVert_map f p 1).trans hz1) rfl
  let Q := q.drop 1
  have hP : P.IsPath := by
    simpa only [P,isPath_copy] using (hp.map (MulAction.toPerm z).injective).drop 1
  have hQ : Q.IsPath := hq.drop 1
  have hPne : P.snd≠Q.snd := by
    change P.getVert 1 ≠ Q.getVert 1
    simpa only [P,Q,getVert_copy,drop_getVert,getVert_map] using
      (show f (p.getVert (1+1)) ≠ q.getVert (1+1) from hz2)
  let H := (pathRoot (X := X) p).map (MulAut.conj z).toMonoidHom ⊓ pathRoot q
  apply two_subgroup_eq_bot_of_diverging_paths ht s hodd P Q hP hQ hPne
    (by simpa only [P,Q,length_copy,drop_length,length_map] using hlen) H
    (((pathRoot_isTwo p).map (MulAut.conj z).toMonoidHom).to_le inf_le_left)
  · intro x hx k hk
    obtain ⟨r,hr,rfl⟩ := hx.1
    have hfix := (Subgroup.pCoreIn_le 2 (pathFixer (X := X) p)) hr
    have hk' : 1+k ≤ p.length := by
      simp only [P,length_copy,drop_length,length_map] at hk
      omega
    simp only [P,getVert_copy,drop_getVert,getVert_map]
    change (z*r*z⁻¹) • (z • p.getVert (1+k))=z • p.getVert (1+k)
    rw [mul_smul,mul_smul,inv_smul_smul,hfix (1+k) hk']
  · intro x hx k hk
    have hfix := (Subgroup.pCoreIn_le 2 (pathFixer (X := X) q)) hx.2
    have hk' : 1+k≤q.length := by
      simp only [Q,drop_length] at hk
      omega
    simpa only [Q,drop_getVert] using hfix (1+k) hk'

end Theory.GroupTheory.WeakBNPair.RegularTree
