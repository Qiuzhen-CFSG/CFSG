module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Census
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourPaths.Apartment
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.FourGeodesic
public import Theory.GroupAction.RankTwoCosetGeometry.ExtensionGeometry

/-!
# Smallness and quadrangle geometry for full unitary-four extensions

The native matrix five-path action descends through the actual injective
SU₄ projection and transfers across the whole marked overlap to every
faithful completion. Thickness and five-path transitivity exclude cycles
shorter than eight, so four-walks are geodesic. The full extension order
bound and the unequal-valency census force a collision of four-geodesics.
The resulting literal coset geometry is a generalized quadrangle.

This proves the geometric part of Aschbacher–Smith F.4.6,13,24,
pp.276–280,287. It includes q = 4 and extensions of even outer degree.
It does not identify the quadrangle or its group with the Hermitian model.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo SimpleGraph SimpleGraph.PathTransitivePolygon
open GreenBook.LieModels.UnitaryFour Theory.SpecificGroups.ClassicalUnitary

private theorem four_projection_preimage (m : ℕ) (hm : 1 ≤ m) (i : Bool) :
    (SourceExtension.nativeFamily (P₀ := pointParabolic m hm)
      (P₁ := planeParabolic m hm) i).comap (projection m hm) =
        SmallCompletion.FourPaths.family (MatrixField m) (fieldConj m)
          (fieldConj_involutive m hm) i := by
  cases i <;> exact Subgroup.comap_map_eq_self_of_injective (projection_injective m hm) _

private theorem four_projection_representative (m : ℕ) (hm : 1 ≤ m) (a : ProjectiveGroup m hm) :
    ∃ b : MatrixGroup m hm, (projection m hm b)⁻¹*a ∈
      SourceExtension.nativeFamily (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm) false ⊓
      SourceExtension.nativeFamily (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm) true := by
  obtain ⟨b,rfl⟩ := UnitaryFourFlag.project_surjective (MatrixField m) (standardForm m hm) a
  exact ⟨b, by simp [projection]⟩

/-- The actual projective group is transitive on rooted nonbacktracking
five-paths in its native point/plane coset graph. -/
theorem four_native_rootPathTransitive_five (m : ℕ) (hm : 1 ≤ m) (i : Bool) :
    RootPathTransitive (graph (SourceExtension.nativeFamily
      (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm)))
      (ProjectiveGroup m hm) (base _ i) 5 := by
  let P : Bool → Subgroup (MatrixGroup m hm) := SmallCompletion.FourPaths.family (MatrixField m) (fieldConj m)
    (fieldConj_involutive m hm)
  let Q := SourceExtension.nativeFamily (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm)
  let e := ExtensionGeometry.graphIso P Q (projection m hm)
    (four_projection_preimage m hm) (four_projection_representative m hm)
  have he : e (base P i) = base Q i := ExtensionGeometry.vertex_base P Q _ _ i
  rw [← he]
  exact RootPathTransitive.map_graphIso e (projection m hm)
    (ExtensionGeometry.vertex_smul P Q _ _) (SmallCompletion.FourPaths.rootPathTransitive_five i)

/-- The native action transfers through the full marked extension, including
even outer degree, and the exact whole overlap of an arbitrary completion. -/
theorem four_completion_rootPathTransitive_five (m : ℕ) (hm : 1 ≤ m)
    (E : FourExtension m hm) {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (v : Vertex c.cosetFamily) : RootPathTransitive (graph c.cosetFamily) M v 5 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.cosetFamily v
  rw [← hg]
  exact RootPathTransitive.smul
    (⟨fun g _ _ h => (translationGraphIso c.cosetFamily g).toHom.map_adj h⟩ :
      GraphAction (graph c.cosetFamily) M)
    (four_completion_rootPathTransitive m hm E c hoverlap v.type 5
      (four_native_rootPathTransitive_five m hm v.type)) g

private theorem four_completion_thick (m : ℕ) (hm : 1 ≤ m)
    (E : FourExtension m hm) {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (v a b : Vertex c.cosetFamily) :
    ∃ z, (graph c.cosetFamily).Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hq : 2 ≤ 2^m := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hm
  have hc : 2 < Nat.card ((graph c.cosetFamily).neighborSet v) := by
    rw [four_completion_card_neighbors m hm E c hoverlap v]
    cases v.type <;> simp [fourDegree] <;> nlinarith
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
theorem four_completion_four_geodesic (m : ℕ) (hm : 1 ≤ m)
    (E : FourExtension m hm) {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    {x : Vertex c.cosetFamily} (p : BasedWalk (graph c.cosetFamily) 4 x)
    (hp : p.Nonbacktracking) : (graph c.cosetFamily).dist x p.endpoint = 4 := by
  have ha : GraphAction (graph c.cosetFamily) M :=
    ⟨fun g _ _ h => (translationGraphIso c.cosetFamily g).toHom.map_adj h⟩
  exact four_geodesic_of_cycle_bound (Subgroup.CosetGeometry.RankTwo.connected c.cosetFamily c.generated) (·.type) (fun h => h.1)
    (cycle_bound_of_five_transitive ha (four_completion_thick m hm E c hoverlap)
      (four_completion_rootPathTransitive_five m hm E c hoverlap) (·.type) (fun h => h.1)) p hp

/-- The full extension order bound forces the source smallness condition,
with two distinct geodesics between vertices at distance four. -/
theorem four_completion_small (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m)
    (E : FourExtension m hm) {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    ∃ x y, (graph c.cosetFamily).dist x y = 4 ∧
      ∃ p q : (graph c.cosetFamily).Walk x y,
        p.length = 4 ∧ q.length = 4 ∧ p ≠ q := by
  obtain ⟨p,q,hp,hq,he,hne⟩ := four_completion_four_path_collision m hm hmgt E c hoverlap horder
  refine ⟨_,p.endpoint,four_completion_four_geodesic m hm E c hoverlap p hp,
    p.toWalk,q.toWalk.copy rfl he.symm,BasedWalk.length_toWalk _,?_,?_⟩
  · simp only [Walk.length_copy,BasedWalk.length_toWalk]
  · intro hh
    apply hne
    apply BasedWalk.vertices_injective 4 _
    have hs := congrArg Walk.support hh
    simpa only [Walk.support_copy,BasedWalk.support_toWalk] using hs

/-- F.4.13(1) for the nonbinary four-dimensional unitary extension: the
literal completion graph has girth eight and diameter four. This is a
metric conclusion and does not assert Hermitian identification. -/
theorem four_completion_quadrangle (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m)
    (E : FourExtension m hm) {M : Type*} [Group M] [Finite M]
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
    obtain ⟨z,hz,hza,_⟩ := four_completion_thick m hm E c hoverlap v a a
    exact ⟨z,hz,hza⟩
  exact QuadrangleRecognition.quadrangle_of_small ha (Subgroup.CosetGeometry.RankTwo.connected c.cosetFamily c.generated) hdeg
    (four_completion_rootPathTransitive_five m hm E c hoverlap)
    (·.type) (fun h => h.1) (fun h => (same_orbit_iff c.cosetFamily _ _).mpr h)
    (four_completion_small m hm hmgt E c hoverlap horder)
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
