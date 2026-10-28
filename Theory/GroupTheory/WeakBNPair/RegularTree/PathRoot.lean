module
public import Theory.GroupTheory.WeakBNPair.RegularTree.CartanUniqueness
public import Theory.GroupTheory.WeakBNPair.RegularTree.LocalRootAction
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Local root actions from long-path radicals

Transitivity on paths of length r+1 makes an r-path stabilizer transitive on
the neighbors at its endpoint other than the preceding vertex. Acyclicity
ensures that each such exit really extends the path. If that stabilizer is
the product of its two-core and a Cartan fixing a chosen exit, the two-core
itself is transitive there. Together with the chosen involution this constructs
the local root action, with root literally O₂ of the long-path stabilizer.

The path-stabilizer product remains an explicit premise. Neither a Borel
Sylow nor an arbitrary transitive subgroup is substituted for this root.
Source: DGS, *Groups and Graphs* (1985), Part II, (14.1) and the root-group
notation after (14.2), printed pp.210--211.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
open scoped Pointwise
variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

/-- Rooted (r+1)-path transitivity gives the actual orbit of an r-path stabilizer on its exits. -/
theorem pathFixer_transitive_exits (htree : Γ.IsAcyclic)
    {d a : V} (p : Γ.Walk d a) (hp : p.IsPath)
    (htrans : BasedPathTransitive (X := X) Γ (p.length+1))
    {c z : V} (hc : Γ.Adj a c) (hcprev : c ≠ p.penultimate)
    (hz : Γ.Adj a z) (hzprev : z ≠ p.penultimate) :
    ∃ g ∈ pathFixer (X := X) p, g • c = z := by
  have hcnew : c ∉ p.support := fun hm =>
    hcprev (htree.eq_penultimate_of_adj_end hp hc hm)
  have hznew : z ∉ p.support := fun hm =>
    hzprev (htree.eq_penultimate_of_adj_end hp hz hm)
  obtain ⟨g, hg⟩ := htrans (p.concat hc) (p.concat hz)
    (hp.concat hcnew hc) (hp.concat hznew hz)
    (by simp only [length_concat]) (by simp only [length_concat])
  refine ⟨g, ?_, ?_⟩
  · intro k hk
    have hh := hg k (by omega)
    simpa only [concat_eq_append, getVert_append', if_pos hk] using hh
  · have hh := hg (p.length+1) le_rfl
    have hce : (p.concat hc).getVert (p.length+1) = c := by
      simpa only [length_concat] using (p.concat hc).getVert_length
    have hze : (p.concat hz).getVert (p.length+1) = z := by
      simpa only [length_concat] using (p.concat hz).getVert_length
    rwa [hce, hze] at hh

/-- The root is the embedded two-core of the actual long-path stabilizer. -/
def pathRoot {d a : V} (p : Γ.Walk d a) : Subgroup X :=
  (pathFixer (X := X) p).pCoreIn 2

/-- The long-path radical is a two-group. -/
theorem pathRoot_isTwo {d a : V} (p : Γ.Walk d a) :
    IsPGroup 2 (pathRoot (X := X) p) := Subgroup.isPGroup_pCoreIn 2 _

/-- The long-path root fixes the endpoint and its preceding vertex. -/
theorem pathRoot_fixes {d a : V} (p : Γ.Walk d a) :
    pathRoot (X := X) p ≤ MulAction.stabilizer X a ⊓
      MulAction.stabilizer X p.penultimate := by
  intro x hx
  have hf := Subgroup.pCoreIn_le 2 (pathFixer (X := X) p) hx
  constructor
  · change x • a = a
    have he := hf p.length le_rfl
    simpa only [getVert_length] using he
  · exact hf (p.length-1) (Nat.sub_le _ _)

/-- The actual product with a Cartan fixing the chosen exit puts the entire exit orbit in the path radical. -/
theorem pathRoot_transitive_exits (htree : Γ.IsAcyclic)
    {d a : V} (p : Γ.Walk d a) (hp : p.IsPath)
    (htrans : BasedPathTransitive (X := X) Γ (p.length+1))
    (K : Subgroup X) {c : V} (hc : Γ.Adj a c) (hcprev : c ≠ p.penultimate)
    (hKc : ∀ k ∈ K, k • c = c)
    (hfactor : (pathFixer (X := X) p : Set X) =
      (pathRoot (X := X) p : Set X) * (K : Set X)) :
    ∀ z, Γ.Adj a z → z ≠ p.penultimate → ∃ r ∈ pathRoot (X := X) p, r • c = z := by
  intro z hz hzprev
  obtain ⟨g, hg, hgz⟩ := pathFixer_transitive_exits htree p hp htrans hc hcprev hz hzprev
  rw [show g ∈ pathFixer (X := X) p ↔ g ∈ (pathFixer (X := X) p : Set X) from Iff.rfl,
    hfactor] at hg
  obtain ⟨r, hr, k, hk, rfl⟩ := hg
  exact ⟨r, hr, by simpa only [mul_smul, hKc k hk] using hgz⟩

/-- An involution and the genuine long-path radical give the local root-action data. -/
def pathRootAction (htree : Γ.IsAcyclic)
    {d a : V} (p : Γ.Walk d a) (hp : p.IsPath) (hpnil : ¬ p.Nil)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (htrans : BasedPathTransitive (X := X) Γ (p.length+1))
    (K : Subgroup X) (t : X) (htfix : t • a = a)
    (htmove : t • p.penultimate ≠ p.penultimate) (htsq : t*t=1)
    (hKc : ∀ k ∈ K, k • (t • p.penultimate) = t • p.penultimate)
    (hfactor : (pathFixer (X := X) p : Set X) =
      (pathRoot (X := X) p : Set X) * (K : Set X))
    (hthick : ∃ z, Γ.Adj a z ∧ z ≠ p.penultimate ∧ z ≠ t • p.penultimate) :
    LocalRootAction (X := X) Γ where
  a := a
  b := p.penultimate
  c := t • p.penultimate
  adj_b := (p.adj_penultimate hpnil).symm
  adj_c := by simpa only [htfix] using hact t (p.adj_penultimate hpnil).symm
  distinct := htmove.symm
  reflection := t
  fixes_a := htfix
  sends_b := rfl
  sends_c := by rw [← mul_smul, htsq, one_smul]
  root := pathRoot p
  root_fixes := pathRoot_fixes p
  transitive := pathRoot_transitive_exits htree p hp htrans K
    (by simpa only [htfix] using hact t (p.adj_penultimate hpnil).symm)
    htmove hKc hfactor
  thick := hthick

end Theory.GroupTheory.WeakBNPair.RegularTree
