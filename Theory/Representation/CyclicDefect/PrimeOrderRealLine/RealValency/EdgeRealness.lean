module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.Tree

/-!
# Real edge characters from the literal tree incidence

The unsigned incidence map of a finite forest is injective over every abelian
additive group. Indeed, the support of a nonzero kernel vector would be a
nonempty forest. A longest path gives a leaf, whose incidence equation then
has exactly one nonzero summand.

Apply this to the difference between each actual lifted edge character and
its complex conjugate. Real ordinary rows give zero incidence sums, so every
edge value on a regular element is real. This is the all-real-vertices case
of the tree rigidity used in Feit, VII.9.2 (p.307), expressed directly using
the supplied decomposition identities. It does not prove real valency:
Feit VII.2.20, VII.2.23--24 still require the serial-module argument.
-/

public section
open scoped Classical BigOperators

namespace Representation.CyclicDefect.PrimeOrderRealLine
namespace RealValency

private theorem forest_leaf {V : Type*} [Fintype V] (H : SimpleGraph V)
    (ha : H.IsAcyclic) {a b : V} (hab : H.Adj a b) :
    ∃ u w, H.Adj u w ∧ ∀ z, H.Adj u z → z = w := by
  let : Nonempty V := ⟨a⟩
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
  have hnil : ¬p.Nil := by
    have hlen := hmax _ _ (SimpleGraph.Walk.cons hab (.nil)) (by simpa using hab.ne)
    intro hn
    have hz := hn.length_eq_zero
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hlen
    omega
  refine ⟨u, p.snd, p.adj_snd hnil, ?_⟩
  intro z hz
  apply ha.eq_snd_of_adj_start hp hz
  have hn : ¬(p.cons hz.symm).IsPath := by
    intro hpath
    have h := hmax _ _ (p.cons hz.symm) hpath
    simp only [SimpleGraph.Walk.length_cons] at h
    omega
  by_contra hnot
  exact hn (hp.cons hnot)

/-- The unsigned incidence map of a forest has zero kernel. -/
theorem incidence_kernel {V E A : Type*} [Fintype V] [Fintype E]
    [AddCommGroup A] (left right : E → V)
    (hne : ∀ e, left e ≠ right e)
    (hinj : Function.Injective (fun e => s(left e, right e)))
    (hforest : (SimpleGraph.fromEdgeSet (Set.range fun e => s(left e, right e))).IsAcyclic)
    (f : E → A)
    (hsum : ∀ v, (∑ e, if v = left e ∨ v = right e then f e else 0) = 0) :
    ∀ e, f e = 0 := by
  classical
  intro e
  by_contra he
  let H : SimpleGraph V := SimpleGraph.fromEdgeSet
    {q | ∃ i, f i ≠ 0 ∧ s(left i, right i) = q}
  have hsub : H ≤ SimpleGraph.fromEdgeSet (Set.range fun i => s(left i, right i)) :=
    SimpleGraph.fromEdgeSet_mono (by rintro q ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)
  have hedge : H.Adj (left e) (right e) := ⟨⟨e, he, rfl⟩, hne e⟩
  obtain ⟨v, w, hvw, hleaf⟩ := forest_leaf H (hforest.anti hsub) hedge
  obtain ⟨i, hi, hpair⟩ := hvw.1
  have hvi : v = left i ∨ v = right i := by
    have : v ∈ s(left i, right i) := by rw [hpair]; simp
    exact Sym2.mem_iff.mp this
  have huniq : ∀ j, j ≠ i →
      (if v = left j ∨ v = right j then f j else 0) = 0 := by
    intro j hji
    split_ifs with hvj
    · by_contra hj
      have hpj : s(left j, right j) = s(v, w) := by
        rcases hvj with hvj | hvj
        · have hadj : H.Adj v (right j) := by
            rw [hvj]
            exact ⟨⟨j, hj, rfl⟩, hne j⟩
          rw [← hvj, hleaf _ hadj]
        · have hadj : H.Adj v (left j) := by
            rw [hvj]
            exact ⟨⟨j, hj, Sym2.eq_swap⟩, (hne j).symm⟩
          rw [← hvj, hleaf _ hadj, Sym2.eq_swap]
      exact hji (hinj (hpj.trans hpair.symm))
    · rfl
  have hz := hsum v
  rw [Finset.sum_eq_single i] at hz
  · exact hi (by simpa [hvi] using hz)
  · intro j _ hji
    exact huniq j hji
  · simp

end RealValency

namespace Tree

variable {K : Type*} [Field K] {G : Type*} [Group G] [Finite G]
    {I : Type*} [Fintype I] {χ : I → ConjClassFunction G} {block : Finset I}
    {p m n : ℕ} {L : CyclicRootLift K m} (t : Tree χ block p n L)

/-- Real ordinary rows force every actual lifted edge character to be real
on regular elements, by injectivity of the forest incidence map. -/
theorem edge_value_real (hreal : ∀ v : {i // i ∈ block}, ∀ g,
    star (χ v.val (ConjClasses.mk g)) = χ v.val (ConjClasses.mk g))
    (e : Fin n) (g : G) (hg : ¬p ∣ orderOf g) :
    star (L.value (t.rep e) g) = L.value (t.rep e) g := by
  classical
  apply sub_eq_zero.mp
  apply RealValency.incidence_kernel t.left t.right t.endpoints_ne t.edges_injective t.isTree.isAcyclic
    (fun j => star (L.value (t.rep j) g) - L.value (t.rep j) g) _ e
  intro v
  have hs : (∑ j, if v = t.left j ∨ v = t.right j
      then star (L.value (t.rep j) g) else 0) = χ v.val (ConjClasses.mk g) := by
    rw [← hreal v g, t.decomposition g hg v]
    simp only [star_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  calc
    _ = (∑ j, if v = t.left j ∨ v = t.right j then star (L.value (t.rep j) g) else 0) -
        (∑ j, if v = t.left j ∨ v = t.right j then L.value (t.rep j) g else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    _ = 0 := by rw [hs, ← t.decomposition g hg v, sub_self]

end Tree
end Representation.CyclicDefect.PrimeOrderRealLine
