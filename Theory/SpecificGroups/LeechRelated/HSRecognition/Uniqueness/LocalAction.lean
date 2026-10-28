module

public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.Graph
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage.Stabilizers
public import Theory.GroupAction.OrbitFamilyEquivalence

/-!
# Identifying the natural Mathieu action on the neighbors

Under any given isomorphism from the actual zero stabilizer to M₂₂, the
stabilizer of a point in the 22-point suborbit maps to an index-22 subgroup.
The existing intrinsic index-22 recognition theorem identifies that subgroup
with a natural point stabilizer. Orbit--stabilizer coordinates then give an
equivariant bijection from the literal graph neighborhood to `Fin 22`.

This discharges the uniqueness of the degree-22 representation used in the
HS application of Wales, "Uniqueness of the graph of a rank three group",
Pacific J. Math. 30 (1969), p.274. The point and action markings are retained
for the subsequent reconstruction of the 77 hexads.
-/

public section
open MulAction
namespace Sporadic.LeechRelated.HS
attribute [local instance] Classical.propDecidable

private theorem orbit_coordinates {P : Subgroup (Equiv.Perm (Fin 100))}
    (e : stabilizer P (0 : Fin 100) ≃* Sporadic.Mathieu.M22)
    (b : Fin 100) (hb : Nat.card (orbit (stabilizer P (0 : Fin 100)) b) = 22) :
    ∃ f : orbit (stabilizer P (0 : Fin 100)) b ≃ Fin 22,
      ∀ (g : stabilizer P (0 : Fin 100)) x, f (g • x) = e g • f x := by
  let K := stabilizer P (0 : Fin 100)
  have hi : ((stabilizer K b).map e.toMonoidHom).index = 22 := by
    rw [Subgroup.index_map_of_bijective e.bijective, index_stabilizer]
    exact hb
  obtain ⟨y, hy⟩ := Sporadic.Mathieu.m22_index_twenty_two_eq_stabilizer _ hi
  let := Sporadic.Mathieu.m22_isPretransitive
  let f₀ := orbitEquivOfStabilizerMap e b y hy
  let f₁ : orbit Sporadic.Mathieu.M22 y ≃ Fin 22 :=
    (Equiv.setCongr (orbit_eq_univ Sporadic.Mathieu.M22 y)).trans (Equiv.Set.univ _)
  let f := f₀.trans f₁
  have hf (g : K) : f ⟨g • b, mem_orbit b g⟩ = e g • y :=
    orbitEquivOfStabilizerMap_apply e b y hy g
  refine ⟨f, ?_⟩
  intro g x
  obtain ⟨k, hk⟩ := x.property
  have hx : x = ⟨k • b, mem_orbit b k⟩ := Subtype.ext hk.symm
  subst x
  have hg : g • (⟨k • b, mem_orbit b k⟩ : orbit K b) =
      ⟨(g * k) • b, mem_orbit b (g * k)⟩ := Subtype.ext (mul_smul _ _ _).symm
  rw [hg, hf, hf, map_mul, mul_smul]

/-- The 22-point suborbit is the actual natural Mathieu action, with the given
abstract stabilizer marking respected. -/
theorem RankThreeData.neighbor_coordinates {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P)
    (e : stabilizer P (0 : Fin 100) ≃* Sporadic.Mathieu.M22) :
    ∃ f : h.graph.neighborSet 0 ≃ Fin 22,
      ∀ (g : stabilizer P (0 : Fin 100)) (x y : Fin 100)
        (hx : h.graph.Adj 0 x) (hy : h.graph.Adj 0 y),
        g • x = y → f ⟨y, hy⟩ = e g • f ⟨x, hx⟩ := by
  obtain ⟨b, hb⟩ := h.subdegree_twenty_two
  have ho : h.graph.neighborSet 0 = orbit (stabilizer P (0 : Fin 100)) b := by
    ext x
    change Nat.card (orbit (stabilizer P (0 : Fin 100)) x) = 22 ↔
      x ∈ orbit (stabilizer P (0 : Fin 100)) b
    constructor
    · intro hx
      rw [← h.suborbit_eq_of_card_eq (hx.trans hb.symm)]
      exact mem_orbit_self _
    · intro hx
      rw [orbit_eq_iff.mpr hx]
      exact hb
  obtain ⟨f, hf⟩ := orbit_coordinates e b hb
  refine ⟨(Equiv.setCongr ho).trans f, ?_⟩
  intro g x y hx hy hxy
  have he : (Equiv.setCongr ho) ⟨y, hy⟩ = g • (Equiv.setCongr ho) ⟨x, hx⟩ :=
    Subtype.ext hxy.symm
  change f ((Equiv.setCongr ho) ⟨y, hy⟩) = e g • f ((Equiv.setCongr ho) ⟨x, hx⟩)
  rw [he, hf]
end Sporadic.LeechRelated.HS
