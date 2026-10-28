module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FivePaths
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.FourGeodesic

/-!
# Smallness and quadrangle geometry for full PSU₅(4) extensions

Native five-path transitivity transfers through the whole marked overlap.
The 65/17 degrees give thickness and exclude cycles shorter than eight.
The genuine full-extension bound forces two distinct four-geodesics with
the same endpoints, hence the literal coset graph is a generalized
quadrangle. This is the geometric part of Aschbacher–Smith F.4.6,13,24
(`refs/quasithin.pdf`, pp.276–280,287); Hermitian identification is separate.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo SimpleGraph SimpleGraph.PathTransitivePolygon

/-- The native action transfers through the full marked extension, including
even outer degree, and the exact whole overlap of an arbitrary completion. -/
theorem five_completion_rootPathTransitive_five (U : GreenBook.UnitaryFive.Model 4)
    (E : FiveExtension U) {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (v : Vertex c.cosetFamily) : RootPathTransitive (graph c.cosetFamily) M v 5 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.cosetFamily v
  rw [← hg]
  exact RootPathTransitive.smul
    (⟨fun g _ _ h => (translationGraphIso c.cosetFamily g).toHom.map_adj h⟩ :
      GraphAction (graph c.cosetFamily) M)
    (E.completion_rootPathTransitive_of_native_without_generation (five_conj_injective U) c hoverlap v.type 5
      (five_native_rootPathTransitive_five U v.type)) g

private theorem five_completion_thick (U : GreenBook.UnitaryFive.Model 4)
    (E : FiveExtension U) {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (v a b : Vertex c.cosetFamily) :
    ∃ z, (graph c.cosetFamily).Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hc : 2 < Nat.card ((graph c.cosetFamily).neighborSet v) := by
    rw [five_completion_card_neighbors U E c hoverlap v]
    cases v.type <;> decide
  have : Finite ((graph c.cosetFamily).neighborSet v) := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite ((graph c.cosetFamily).neighborSet v)
  rw [Nat.card_eq_fintype_card] at hc
  obtain ⟨x,y,z,hxy,hxz,hyz⟩ := Fintype.two_lt_card_iff.mp hc
  by_contra hh
  push Not at hh
  have hx : x.val = a ∨ x.val = b := by
    by_cases ha : x.val = a
    · exact Or.inl ha
    · exact Or.inr (hh x.val x.property ha)
  have hy : y.val = a ∨ y.val = b := by
    by_cases ha : y.val = a
    · exact Or.inl ha
    · exact Or.inr (hh y.val y.property ha)
  have hz : z.val = a ∨ z.val = b := by
    by_cases ha : z.val = a
    · exact Or.inl ha
    · exact Or.inr (hh z.val z.property ha)
  have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hxz' : x.val ≠ z.val := fun h => hxz (Subtype.ext h)
  have hyz' : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    rcases hz with hz | hz <;> simp_all

/-- Every nonbacktracking four-walk in a faithful unitary completion is
geodesic, independently of the order bound. -/
theorem five_completion_four_geodesic (U : GreenBook.UnitaryFive.Model 4)
    (E : FiveExtension U) {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    {x : Vertex c.cosetFamily} (p : BasedWalk (graph c.cosetFamily) 4 x)
    (hp : p.Nonbacktracking) : (graph c.cosetFamily).dist x p.endpoint = 4 := by
  have ha : GraphAction (graph c.cosetFamily) M :=
    ⟨fun g _ _ h => (translationGraphIso c.cosetFamily g).toHom.map_adj h⟩
  exact four_geodesic_of_cycle_bound (Subgroup.CosetGeometry.RankTwo.connected c.cosetFamily c.generated) (·.type) (fun h => h.1)
    (cycle_bound_of_five_transitive ha (five_completion_thick U E c hoverlap)
      (five_completion_rootPathTransitive_five U E c hoverlap) (·.type) (fun h => h.1)) p hp

/-- The full extension order bound forces the source smallness condition,
with two distinct geodesics between vertices at distance four. -/
theorem five_completion_small (U : GreenBook.UnitaryFive.Model 4)
    (E : FiveExtension U) {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    ∃ x y, (graph c.cosetFamily).dist x y = 4 ∧
      ∃ p q : (graph c.cosetFamily).Walk x y,
        p.length = 4 ∧ q.length = 4 ∧ p ≠ q := by
  obtain ⟨p,q,hp,hq,he,hne⟩ := five_completion_four_path_collision U E c hoverlap horder false
  refine ⟨_,p.endpoint,five_completion_four_geodesic U E c hoverlap p hp,
    p.toWalk,q.toWalk.copy rfl he.symm,BasedWalk.length_toWalk _,?_,?_⟩
  · simp only [Walk.length_copy,BasedWalk.length_toWalk]
  · intro hh
    apply hne
    apply BasedWalk.vertices_injective 4 _
    have hs := congrArg Walk.support hh
    simpa only [Walk.support_copy,BasedWalk.support_toWalk] using hs

/-- F.4.13(1) for the fixed projective unitary-five extension: the
literal completion graph has girth eight and diameter four. This is a
metric conclusion and does not assert Hermitian identification. -/
theorem five_completion_quadrangle (U : GreenBook.UnitaryFive.Model 4)
    (E : FiveExtension U) {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    (∀ v (p : (graph c.cosetFamily).Walk v v), p.IsCycle → 8 ≤ p.length) ∧
      (∀ v w, (graph c.cosetFamily).dist v w ≤ 4) ∧
      (∃ v, ∃ p : (graph c.cosetFamily).Walk v v, p.IsCycle ∧ p.length = 8) := by
  have ha : GraphAction (graph c.cosetFamily) M :=
    ⟨fun g _ _ h => (translationGraphIso c.cosetFamily g).toHom.map_adj h⟩
  have hdeg : BasedWalk.HasTwoNeighbors (graph c.cosetFamily) := by
    intro v a
    obtain ⟨z,hz,hza,_⟩ := five_completion_thick U E c hoverlap v a a
    exact ⟨z,hz,hza⟩
  exact QuadrangleRecognition.quadrangle_of_small ha (Subgroup.CosetGeometry.RankTwo.connected c.cosetFamily c.generated) hdeg
    (five_completion_rootPathTransitive_five U E c hoverlap)
    (·.type) (fun h => h.1) (fun h => (same_orbit_iff c.cosetFamily _ _).mpr h)
    (five_completion_small U E c hoverlap horder)
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
