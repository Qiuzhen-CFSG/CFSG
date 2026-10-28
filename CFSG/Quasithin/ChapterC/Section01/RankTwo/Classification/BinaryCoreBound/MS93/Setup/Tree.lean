module

public import Stellmacher.PushingUp.AmalgamGraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The MS93 free-amalgam graph is a tree

The right-coset graph of `M *_R Holomorph R` is acyclic, hence a tree by the
existing connectedness theorem. In particular, any two vertices have exactly
one simple path. These conclusions hold for every subgroup `R` of any group
`M`; neither the factors nor the graph need be finite.

For acyclicity, start with one edge of a hypothetical cycle. Following the
remaining trail produces an alternating word in the two factors: successive
letters are the ratios of representatives of consecutive edges. Avoidance of
the incoming edge ensures that every letter lies outside the amalgamated
subgroup. The endpoint would force this reduced word into the factor opposite
its first letter, contrary to the pushout normal-form theorem. This uses the
original right cosets, carrier and embeddings throughout.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), Section 2.0 and the tree assertion of 2.1(i), printed pp.854--855.
The other assertions of 2.1(i), edge transitivity and failure of vertex
transitivity, are already proved in `Stellmacher.PushingUp.AmalgamGraph`.
-/

public section

open Monoid Monoid.CoprodI Monoid.PushoutI

namespace Stellmacher.PushingUp.AmalgamGraph

universe u
variable {M : Type u} [Group M] (R : Subgroup M)

private def other : Side → Side
  | .m => .h
  | .h => .m

@[simp] private theorem other_other (i : Side) : other (other i) = i := by cases i <;> rfl
@[simp] private theorem other_ne (i : Side) : other i ≠ i := by cases i <;> decide

private def vertex (i : Side) (x : FreeAmalgam R) : Vertex R :=
  match i with
  | .m => mVertex R x
  | .h => hVertex R x

private theorem vertex_side {i j : Side} {x y : FreeAmalgam R}
    (h : vertex R i x = vertex R j y) : i = j := by
  cases i <;> cases j <;> simp_all [vertex, mVertex, hVertex]

set_option backward.isDefEq.respectTransparency false in
private theorem vertex_eq_iff (i : Side) (x y : FreeAmalgam R) :
    vertex R i x = vertex R i y ↔ x * y⁻¹ ∈ (of (φ := diagram R) i).range := by
  cases i
  · change (Sum.inl (rightCoset (Mbar R) x) : Vertex R) =
      Sum.inl (rightCoset (Mbar R) y) ↔ _
    rw [Sum.inl.injEq]
    change Quotient.mk _ x = Quotient.mk _ y ↔ _
    rw [Quotient.eq, QuotientGroup.rightRel_apply]
    exact ⟨fun h => by simpa only [Mbar, embedM, mul_inv_rev, inv_inv] using (Subgroup.inv_mem _ h),
      fun h => by simpa only [Mbar, embedM, mul_inv_rev, inv_inv] using (Subgroup.inv_mem _ h)⟩
  · change (Sum.inr (rightCoset (Hbar R) x) : Vertex R) =
      Sum.inr (rightCoset (Hbar R) y) ↔ _
    rw [Sum.inr.injEq]
    change Quotient.mk _ x = Quotient.mk _ y ↔ _
    rw [Quotient.eq]
    rw [QuotientGroup.rightRel_apply]
    exact ⟨fun h => by simpa only [Hbar, embedH, mul_inv_rev, inv_inv] using (Subgroup.inv_mem _ h),
      fun h => by simpa only [Hbar, embedH, mul_inv_rev, inv_inv] using (Subgroup.inv_mem _ h)⟩

private theorem adjacent_vertex (i : Side) {u v : Vertex R}
    {x : FreeAmalgam R} (hu : u = vertex R i x)
    (h : (cosetGraph R).Adj u v) :
    ∃ y, u = vertex R i y ∧ v = vertex R (other i) y := by
  obtain ⟨y, h | h⟩ := (adjacent_iff_exists_common R u v).mp
    ((cosetGraph_adj R u v).mp h)
  · cases i with
    | m => exact ⟨y, h⟩
    | h => simp [hu, vertex, mVertex, hVertex] at h
  · cases i with
    | h => exact ⟨y, h⟩
    | m => simp [hu, vertex, mVertex, hVertex] at h

private theorem of_diagram_mem_other (i : Side) (t : R) :
    of (φ := diagram R) i (diagram R i t) ∈
      (of (φ := diagram R) (other i)).range := by
  refine ⟨diagram R (other i) t, ?_⟩
  simp only [of_apply_eq_base]

/-- A reduced word whose first letter is not in a given factor cannot
represent an element of that factor unless it is empty. -/
private theorem reduced_empty_of_mem_factor
    {w : Word (factor R)} (hw : Reduced (diagram R) w)
    (i : Side) (hi : w.fstIdx ≠ some i)
    (hp : ofCoprodI w.prod ∈ (of (φ := diagram R) i).range) :
    w = .empty := by
  classical
  obtain ⟨t, ht⟩ := hp
  by_cases hb : t ∈ (diagram R i).range
  · apply hw.eq_empty_of_mem_range (diagram_injective R)
    obtain ⟨s, rfl⟩ := hb
    exact ⟨s, by simpa only [of_apply_eq_base] using ht⟩
  · have ht1 : t⁻¹ ≠ 1 := by
      intro he
      apply hb
      exact ⟨1, by simp [inv_eq_one.mp he]⟩
    let w' := Word.cons t⁻¹ w hi ht1
    have hw' : Reduced (diagram R) w' := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simpa only [Subgroup.inv_mem_iff] using hb
      · exact hw g hg
    have he := hw'.eq_empty_of_mem_range (diagram_injective R) (by
      refine ⟨1, ?_⟩
      simp only [w', Word.prod_cons, map_mul, ofCoprodI_of, map_inv, ← ht,
        inv_mul_cancel, map_one])
    have := congrArg Word.toList he
    simp [w', Word.cons, Word.empty] at this

/-- Lift a trail, with a specified incoming edge which it avoids, to a
reduced word. The product is the ratio of the initial and final edge
representatives, and the word has exactly one letter per step of the trail. -/
private theorem walk_word {u v : Vertex R} (p : (cosetGraph R).Walk u v)
    (hp : p.IsTrail) (i : Side) (x : FreeAmalgam R)
    (hu : u = vertex R i x)
    (he : s(u, vertex R (other i) x) ∉ p.edges) :
    ∃ (w : Word (factor R)) (j : Side) (y : FreeAmalgam R),
      Reduced (diagram R) w ∧ w.fstIdx ≠ some (other i) ∧
      w.toList.length = p.length ∧ ofCoprodI w.prod = x * y⁻¹ ∧
      v = vertex R j y := by
  induction p generalizing i x with
  | nil =>
    exact ⟨.empty, i, x, by simp [Reduced, Word.empty], by simp [Word.fstIdx],
      rfl, by simp, hu⟩
  | @cons u v z h p ih =>
    obtain ⟨y, huy, hvy⟩ := adjacent_vertex R i hu h
    have hxy := (vertex_eq_iff R i x y).mp (hu.symm.trans huy)
    obtain ⟨t, ht⟩ := hxy
    have htbase : t ∉ (diagram R i).range := by
      rintro ⟨s, rfl⟩
      have hother : x * y⁻¹ ∈ (of (φ := diagram R) (other i)).range := by
        rw [← ht]
        exact of_diagram_mem_other R i s
      have hvx : v = vertex R (other i) x :=
        hvy.trans ((vertex_eq_iff R (other i) x y).mpr hother).symm
      apply he
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
      exact Or.inl (congrArg (fun a => s(u, a)) hvx.symm)
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact htbase ⟨1, map_one _⟩
    obtain ⟨hp', he'⟩ := (SimpleGraph.Walk.isTrail_cons h p).mp hp
    have hin : s(v, vertex R (other (other i)) y) ∉ p.edges := by
      simpa only [other_other, ← huy, Sym2.eq_swap] using he'
    obtain ⟨w, j, a, hw, hwi, hwlen, hwprod, hza⟩ :=
      ih hp' (other i) y hvy hin
    have hwi' : w.fstIdx ≠ some i := by simpa using hwi
    refine ⟨Word.cons t w hwi' ht1, j, a, ?_, ?_, ?_, ?_, hza⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact htbase
      · exact hw g hg
    · simpa only [Word.fstIdx_cons, ne_eq, Option.some.injEq] using (other_ne i).symm
    · simpa only [Word.cons_toList, List.length_cons, SimpleGraph.Walk.length_cons] using
        congrArg Nat.succ hwlen
    · simp only [Word.prod_cons, map_mul, ofCoprodI_of, hwprod, ht]
      group

/-- The actual free-amalgam right-coset graph has no cycles. -/
theorem cosetGraph_isAcyclic : (cosetGraph R).IsAcyclic := by
  intro u p hp
  cases p with
  | nil => exact hp.ne_nil rfl
  | @cons a v b h p =>
    have hedge : ∃ (i : Side) (x : FreeAmalgam R),
        u = vertex R i x ∧ v = vertex R (other i) x := by
      obtain ⟨x, hx | hx⟩ := (adjacent_iff_exists_common R u v).mp
        ((cosetGraph_adj R u v).mp h)
      · exact ⟨.m, x, hx⟩
      · exact ⟨.h, x, hx⟩
    obtain ⟨i, x, hux, hvx⟩ := hedge
    obtain ⟨hp', he⟩ := (SimpleGraph.Walk.isTrail_cons h p).mp hp.isTrail
    obtain ⟨w, j, y, hw, hwi, hlen, hprod, huy⟩ :=
      walk_word R p hp' (other i) x hvx
        (by simpa only [other_other, ← hux, Sym2.eq_swap] using he)
    have hj : j = i := vertex_side R (huy.symm.trans hux)
    subst j
    have hmem := (vertex_eq_iff R i x y).mp (hux.symm.trans huy)
    rw [← hprod] at hmem
    have hempty := reduced_empty_of_mem_factor R hw i (by simpa using hwi) hmem
    have hzero : p.length = 0 := by simpa [hempty] using hlen.symm
    have := hp.three_le_length
    simp only [SimpleGraph.Walk.length_cons, hzero] at this
    omega

/-- The tree assertion of MS93 2.1(i), for the existing free holomorph amalgam.
No Sylow, characteristic-subgroup or finiteness hypothesis is required. -/
theorem cosetGraph_isTree : (cosetGraph R).IsTree :=
  ⟨cosetGraph_connected R, cosetGraph_isAcyclic R⟩

/-- Between any two vertices of the free-amalgam graph there is exactly one
simple path, including the empty path when the endpoints coincide. -/
theorem cosetGraph_existsUnique_path (u v : Vertex R) :
    ∃! p : (cosetGraph R).Walk u v, p.IsPath :=
  (cosetGraph_isTree R).existsUnique_path u v

end Stellmacher.PushingUp.AmalgamGraph
