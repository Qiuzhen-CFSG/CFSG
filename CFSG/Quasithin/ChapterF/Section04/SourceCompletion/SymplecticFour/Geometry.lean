module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.Paths
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.FiveGirth
public import Theory.GroupAction.RankTwoCosetGeometry.QuadrangleCount

/-!
# Quadrangle geometry and exact order of symplectic extension completions

Five-path transitivity forces girth at least eight and hence geodesicity of
all nonbacktracking four-paths. The order-forced collision is therefore the
source smallness witness, giving diameter four and an eight-cycle. Counting
distinct endpoints of one- and three-paths gives the native lower bound for
each vertex type. The full extension bound forces equality of group orders.
These conclusions do not identify an arbitrary generalized quadrangle with
the symplectic quadrangle; that is the remaining recognition step.

Source: Aschbacher–Smith F.4.6, F.4.13 and F.4.24, printed pp.276–280,
287–288 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
namespace SourceExtension
variable (E : SourceExtension F)

/-- The extension degree cancels from each full endpoint index. -/
theorem index_endpoint (i : Bool) : (E.modelCompletion.cosetFamily i).index =
    (Nat.card F + 1) * (Nat.card F ^ 2 + 1) := by
  let f := ExtensionGeometry.coset FlagPaths.family E.modelCompletion.cosetFamily
    E.innerMap E.innerMap_comap i
  have hi : Function.Injective f := ExtensionGeometry.coset_injective _ _ _ _ i
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨b,rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g,hg⟩ := ExtensionGeometry.representative _ _ E.innerMap_representative b
    exact ⟨(g : Sp F ⧸ FlagPaths.family i),hg i⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm.trans
    (FlagPaths.index_endpoint i)
end SourceExtension

namespace Completion
variable {E : SourceExtension F} {M : Type*} [Group M] (c : Completion E M)

omit [CharP F 2] [Finite F] in
theorem connected : (graph c.cosetFamily).Connected :=
  Subgroup.CosetGeometry.RankTwo.connected c.cosetFamily c.generated

omit [CharP F 2] [Finite F] in
theorem graphAction : GraphAction (graph c.cosetFamily) M where
  map_adj g := (CosetGeometry.translationGraphIso c.cosetFamily g).toHom.map_adj

theorem thick (hc : c.left.range ⊓ c.right.range = c.middle.range) (v a b : Vertex c.cosetFamily) : ∃z,(graph c.cosetFamily).Adj v z ∧ z≠a ∧ z≠b := by
  classical
  let : Finite ((graph c.cosetFamily).neighborSet v) := Nat.finite_of_card_ne_zero
    (by rw [c.card_neighbors hc]; positivity)
  let := Fintype.ofFinite ((graph c.cosetFamily).neighborSet v)
  have hc : 2 < Fintype.card ((graph c.cosetFamily).neighborSet v) := by
    rw [←Nat.card_eq_fintype_card,c.card_neighbors hc]
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  obtain ⟨x,y,z,hxy,hxz,hyz⟩ := Fintype.two_lt_card_iff.mp hc
  by_contra hh
  push Not at hh
  have hx : x.val=a ∨ x.val=b := by
    by_cases ha : x.val=a
    · exact Or.inl ha
    · exact Or.inr (hh x.val x.property ha)
  have hy : y.val=a ∨ y.val=b := by
    by_cases ha : y.val=a
    · exact Or.inl ha
    · exact Or.inr (hh y.val y.property ha)
  have hz : z.val=a ∨ z.val=b := by
    by_cases ha : z.val=a
    · exact Or.inl ha
    · exact Or.inr (hh z.val z.property ha)
  have hxy' : x.val≠y.val := fun h => hxy (Subtype.ext h)
  have hxz' : x.val≠z.val := fun h => hxz (Subtype.ext h)
  have hyz' : y.val≠z.val := fun h => hyz (Subtype.ext h)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;> simp_all

theorem hasTwoNeighbors (hc : c.left.range ⊓ c.right.range = c.middle.range) : BasedWalk.HasTwoNeighbors (graph c.cosetFamily) := by
  intro v a
  obtain ⟨z,hz,hza,_⟩ := c.thick hc v a a
  exact ⟨z,hz,hza⟩

theorem cycle_length_ge_eight (ho : c.left.range ⊓ c.right.range = c.middle.range)
    (v : Vertex c.cosetFamily) (p : (graph c.cosetFamily).Walk v v) (hp : p.IsCycle) :
    8 ≤ p.length :=
  cycle_bound_of_five_transitive c.graphAction (c.thick ho) (c.all_rootPathTransitive_five ho)
    (·.type) (fun h => h.1) v p hp

/-- Four-paths are geodesics before the order bound is used. -/
theorem four_path_geodesic (ho : c.left.range ⊓ c.right.range = c.middle.range)
    {v : Vertex c.cosetFamily} (p : BasedWalk (graph c.cosetFamily) 4 v)
    (hp : p.Nonbacktracking) : (graph c.cosetFamily).dist v p.endpoint = 4 :=
  geodesic_of_nonbacktracking_of_double_le_girth c.connected (c.cycle_length_ge_eight ho) p hp

/-- The actual F.4.7 smallness witness, with two distinct geodesics to an opposite. -/
theorem small [Finite M] (ho : c.left.range ⊓ c.right.range = c.middle.range)
    (hq : 2 < Nat.card F) (hcard : Nat.card M ≤ Nat.card E.carrier)
    (v : Vertex c.cosetFamily) :
    ∃ w, (graph c.cosetFamily).dist v w = 4 ∧
      ∃ p q : (graph c.cosetFamily).Walk v w,
        p.length = 4 ∧ q.length = 4 ∧ p ≠ q := by
  obtain ⟨p,q,hp,hq',hne,he⟩ := c.four_path_collision ho hq hcard v
  refine ⟨p.endpoint,c.four_path_geodesic ho p hp,p.toWalk,
    q.toWalk.copy rfl he.symm,BasedWalk.length_toWalk _,?_,?_⟩
  · simp only [Walk.length_copy,BasedWalk.length_toWalk]
  · intro hh
    apply hne
    apply BasedWalk.vertices_injective 4 v
    have hs := congrArg Walk.support hh
    simpa only [Walk.support_copy,BasedWalk.support_toWalk] using hs

/-- The geometry is a thick generalized quadrangle; no native identification
is included in this metric statement. -/
theorem quadrangle [Finite M] (ho : c.left.range ⊓ c.right.range = c.middle.range)
    (hq : 2 < Nat.card F) (hcard : Nat.card M ≤ Nat.card E.carrier) :
    (∀ v (p : (graph c.cosetFamily).Walk v v), p.IsCycle → 8 ≤ p.length) ∧
    (∀ v w, (graph c.cosetFamily).dist v w ≤ 4) ∧
    (∃ v, ∃ p : (graph c.cosetFamily).Walk v v, p.IsCycle ∧ p.length = 8) := by
  apply QuadrangleRecognition.quadrangle_of_small c.graphAction c.connected (c.hasTwoNeighbors ho)
    (c.all_rootPathTransitive_five ho) (·.type) (fun h => h.1)
    (fun h => (same_orbit_iff c.cosetFamily _ _).mpr h)
  exact ⟨base c.cosetFamily false,c.small ho hq hcard _⟩

/-- Source F.4.13's exact point and line counts for the actual completion. -/
theorem index_endpoint [Finite M] (ho : c.left.range ⊓ c.right.range = c.middle.range)
    (hq : 2 < Nat.card F) (hcard : Nat.card M ≤ Nat.card E.carrier) (i : Bool) :
    (c.cosetFamily i).index = (Nat.card F + 1) * (Nat.card F ^ 2 + 1) := by
  have hquad := c.quadrangle ho hq hcard
  exact index_of_quadrangle_geometry c.cosetFamily c.generated hquad.1 hquad.2.1
    (Nat.card F) (c.card_neighbors ho) i

/-- F.4.13(2), retaining the entire outer extension degree. -/
theorem card_eq [Finite M] (ho : c.left.range ⊓ c.right.range = c.middle.range)
    (hq : 2 < Nat.card F) (hcard : Nat.card M ≤ Nat.card E.carrier) :
    Nat.card M = Nat.card E.carrier := by
  calc
    Nat.card M = Nat.card (c.cosetFamily false) * (c.cosetFamily false).index :=
      (c.cosetFamily false).card_mul_index.symm
    _ = Nat.card (E.modelCompletion.cosetFamily false) *
        (E.modelCompletion.cosetFamily false).index := by
      rw [c.card_endpoint_eq_model,c.index_endpoint ho hq hcard,E.index_endpoint]
    _ = Nat.card E.carrier := (E.modelCompletion.cosetFamily false).card_mul_index

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
