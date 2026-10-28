module
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CommonCover
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The tree of an injective rank-two amalgam

The endpoint ranges in the actual group pushout intersect in exactly the
marked middle group. Their typed coset graph is a tree: a cycle would give a
nonempty reduced word lying in the endpoint opposite its first letter,
contrary to the pushout normal form. No endpoint or completion is assumed
finite. The right-coset representative used in the word proof is the inverse
left-coset vertex in the existing rank-two geometry.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), 2.4--2.5;
Serre, *Arbres, amalgames, SL₂* (1977), p.48. The reduced-word argument extends
the existing MS93 holomorph-amalgam tree proof to arbitrary injective maps.
-/

@[expose] public section
open Monoid Monoid.CoprodI Monoid.PushoutI
open Subgroup.CosetGeometry.RankTwo
namespace Theory.GroupTheory.RankTwoAmalgam.Universal
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R)

/-- Both endpoint maps of the underlying pushout diagram are injective. -/
theorem structureMap_injective (hL : Function.Injective α.left) (hR : Function.Injective α.right) (i : Bool) : Function.Injective (α.structureMap i) := by
  cases i
  · exact hL
  · exact hR

/-- The actual overlap in the universal completion is the marked middle image. -/
theorem overlap_eq (hL : Function.Injective α.left) (hR : Function.Injective α.right) : (left α).range ⊓ (right α).range =
    ((left α).comp α.left).range := by
  have h := inf_of_range_eq_base_range (structureMap_injective α hL hR)
    (by decide : false ≠ true)
  change (of (φ := α.structureMap) false).range ⊓ (of (φ := α.structureMap) true).range =
    ((of (φ := α.structureMap) false).comp (α.structureMap false)).range
  rw [of_comp_eq_base]
  exact h

private theorem family_eq_range (i : Bool) :
    cosetFamily α i = (of (φ := α.structureMap) i).range := by cases i <;> rfl

private abbrev vertex (i : Bool) (x : α.Universal) : Vertex (cosetFamily α) :=
  rightVertex (cosetFamily α) i x

private theorem vertex_side {i j : Bool} {x y : α.Universal}
    (h : vertex α i x = vertex α j y) : i = j :=
  congrArg Subgroup.CosetGeometry.Vertex.type h

private theorem vertex_eq_iff (i : Bool) (x y : α.Universal) :
    vertex α i x = vertex α i y ↔ x * y⁻¹ ∈ (of (φ := α.structureMap) i).range := by
  rw [← family_eq_range]
  exact rightVertex_eq_iff (cosetFamily α) i x y

private theorem edge_representative {v w : Vertex (cosetFamily α)}
    (h : (graph (cosetFamily α)).Adj v w) :
    ∃ (i : Bool) (x : α.Universal), v = vertex α i x ∧ w = vertex α (!i) x := by
  obtain ⟨g, hv, hw⟩ := incident_common_translate (cosetFamily α) h.2
  have ht : w.type = !v.type := by
    have hn := h.1
    cases hv' : v.type <;> cases hw' : w.type <;> simp_all
  refine ⟨v.type, g⁻¹, ?_, ?_⟩
  · simpa only [vertex, rightVertex, inv_inv] using hv.symm
  · simpa only [vertex, rightVertex, inv_inv, ht] using hw.symm

private theorem adjacent_vertex (i : Bool) {u v : Vertex (cosetFamily α)}
    {x : α.Universal} (hu : u = vertex α i x)
    (h : (graph (cosetFamily α)).Adj u v) :
    ∃ y, u = vertex α i y ∧ v = vertex α (!i) y := by
  obtain ⟨j, y, huj, hv⟩ := edge_representative α h
  have hj : j = i := vertex_side α (huj.symm.trans hu)
  subst j
  exact ⟨y, huj, hv⟩

private theorem of_diagram_mem_other (i : Bool) (t : B) :
    of (φ := α.structureMap) i (α.structureMap i t) ∈
      (of (φ := α.structureMap) (!i)).range := by
  refine ⟨α.structureMap (!i) t, ?_⟩
  simp only [of_apply_eq_base]

/-- A reduced word cannot belong to the factor opposite its first letter. -/
private theorem reduced_empty_of_mem_factor (hL : Function.Injective α.left) (hR : Function.Injective α.right)
    {w : Word (Endpoint (L := L) (R := R))} (hw : Reduced α.structureMap w)
    (i : Bool) (hi : w.fstIdx ≠ some i)
    (hp : ofCoprodI w.prod ∈ (of (φ := α.structureMap) i).range) :
    w = .empty := by
  classical
  obtain ⟨t, ht⟩ := hp
  by_cases hb : t ∈ (α.structureMap i).range
  · apply hw.eq_empty_of_mem_range (structureMap_injective α hL hR)
    obtain ⟨s, rfl⟩ := hb
    exact ⟨s, by simpa only [of_apply_eq_base] using ht⟩
  · have ht1 : t⁻¹ ≠ 1 := by
      intro he
      apply hb
      exact ⟨1, by simp [inv_eq_one.mp he]⟩
    let w' := Word.cons t⁻¹ w hi ht1
    have hw' : Reduced α.structureMap w' := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simpa only [Subgroup.inv_mem_iff] using hb
      · exact hw g hg
    have he := hw'.eq_empty_of_mem_range (structureMap_injective α hL hR) (by
      refine ⟨1, ?_⟩
      simp only [w', Word.prod_cons, map_mul, ofCoprodI_of, map_inv, ← ht,
        inv_mul_cancel, map_one])
    have := congrArg Word.toList he
    simp [w', Word.cons, Word.empty] at this

/-- A trail avoiding its incoming edge determines the actual reduced word
of ratios of successive edge representatives. -/
private theorem walk_word {u v : Vertex (cosetFamily α)}
    (p : (graph (cosetFamily α)).Walk u v) (hp : p.IsTrail)
    (i : Bool) (x : α.Universal) (hu : u = vertex α i x)
    (he : s(u, vertex α (!i) x) ∉ p.edges) :
    ∃ (w : Word (Endpoint (L := L) (R := R))) (j : Bool) (y : α.Universal),
      Reduced α.structureMap w ∧ w.fstIdx ≠ some (!i) ∧
      w.toList.length = p.length ∧ ofCoprodI w.prod = x * y⁻¹ ∧
      v = vertex α j y := by
  induction p generalizing i x with
  | nil =>
    exact ⟨.empty, i, x, by simp [Reduced, Word.empty], by simp [Word.fstIdx],
      rfl, by simp, hu⟩
  | @cons u v z h p ih =>
    obtain ⟨y, huy, hvy⟩ := adjacent_vertex α i hu h
    have hxy := (vertex_eq_iff α i x y).mp (hu.symm.trans huy)
    obtain ⟨t, ht⟩ := hxy
    have htbase : t ∉ (α.structureMap i).range := by
      rintro ⟨s, rfl⟩
      have hother : x * y⁻¹ ∈ (of (φ := α.structureMap) (!i)).range := by
        rw [← ht]
        exact of_diagram_mem_other α i s
      have hvx : v = vertex α (!i) x :=
        hvy.trans ((vertex_eq_iff α (!i) x y).mpr hother).symm
      apply he
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
      exact Or.inl (congrArg (fun a => s(u, a)) hvx.symm)
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact htbase ⟨1, map_one _⟩
    obtain ⟨hp', he'⟩ := (SimpleGraph.Walk.isTrail_cons h p).mp hp
    have hin : s(v, vertex α (!(!i)) y) ∉ p.edges := by
      simpa only [Bool.not_not, ← huy, Sym2.eq_swap] using he'
    obtain ⟨w, j, a, hw, hwi, hwlen, hwprod, hza⟩ :=
      ih hp' (!i) y hvy hin
    have hwi' : w.fstIdx ≠ some i := by simpa only [Bool.not_not] using hwi
    refine ⟨Word.cons t w hwi' ht1, j, a, ?_, ?_, ?_, ?_, hza⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact htbase
      · exact hw g hg
    · simp only [Word.fstIdx_cons, ne_eq, Option.some.injEq]
      cases i <;> decide
    · simpa only [Word.cons_toList, List.length_cons, SimpleGraph.Walk.length_cons] using
        congrArg Nat.succ hwlen
    · simp only [Word.prod_cons, map_mul, ofCoprodI_of, hwprod, ht]
      simp only [mul_assoc, inv_mul_cancel_left]

/-- The actual typed coset graph of the pushout has no cycles. -/
theorem cosetGraph_isAcyclic (hL : Function.Injective α.left) (hR : Function.Injective α.right) : (graph (cosetFamily α)).IsAcyclic := by
  intro u p hp
  cases p with
  | nil => exact hp.ne_nil rfl
  | @cons a v b h p =>
    obtain ⟨i, x, hux, hvx⟩ := edge_representative α h
    obtain ⟨hp', he⟩ := (SimpleGraph.Walk.isTrail_cons h p).mp hp.isTrail
    obtain ⟨w, j, y, hw, hwi, hlen, hprod, huy⟩ :=
      walk_word α p hp' (!i) x hvx
        (by simpa only [Bool.not_not, ← hux, Sym2.eq_swap] using he)
    have hj : j = i := vertex_side α (huy.symm.trans hux)
    subst j
    have hmem := (vertex_eq_iff α i x y).mp (hux.symm.trans huy)
    rw [← hprod] at hmem
    have hempty := reduced_empty_of_mem_factor α hL hR hw i
      (by simpa only [Bool.not_not] using hwi) hmem
    have hzero : p.length = 0 := by simpa [hempty] using hlen.symm
    have := hp.three_le_length
    simp only [SimpleGraph.Walk.length_cons, hzero] at this
    omega

/-- The coset graph of any injective rank-two amalgam is a tree. -/
theorem cosetGraph_isTree (hL : Function.Injective α.left) (hR : Function.Injective α.right) : (graph (cosetFamily α)).IsTree :=
  ⟨connected (cosetFamily α) (generated α), cosetGraph_isAcyclic α hL hR⟩

/-- The original marking identifies the amalgam with its endpoint images
and their whole intersection in the universal completion. -/
noncomputable def markedIso (hL : Function.Injective α.left) (hR : Function.Injective α.right) :
    Iso α (ofSubgroups (left α).range ((left α).range ⊓ (right α).range)
      (right α).range inf_le_left inf_le_right) where
  left := MonoidHom.ofInjective (of_injective (structureMap_injective α hL hR) false)
  right := MonoidHom.ofInjective (of_injective (structureMap_injective α hL hR) true)
  middle := (MonoidHom.ofInjective (f := (left α).comp α.left)
    ((of_injective (structureMap_injective α hL hR) false).comp hL)).trans
      (MulEquiv.subgroupCongr (overlap_eq α hL hR).symm)
  left_commutes b := by apply Subtype.ext; rfl
  right_commutes b := by
    apply Subtype.ext
    exact (DFunLike.congr_fun (compatible α) b).symm

end Theory.GroupTheory.RankTwoAmalgam.Universal
