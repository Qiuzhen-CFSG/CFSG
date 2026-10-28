module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# A transitive subgroup on each definite plane

The kernel of the permutation of the two coordinate planes is an actual
subgroup of M. Compatibility with the natural wreath action proves that it
normalizes both planes. Completing a nonzero binary vector to an SL₂ matrix,
then lifting that matrix through the surjective actor map, proves transitivity
on the three nonidentity elements. Once I=N_G(V₁), this gives an actor in I.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, natural action
on printed pp.1121--1122 and its use in 15.3.38, p.1137.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
variable {G : Type*} [Group G]

/-- The actual subgroup of M with trivial permutation of the two planes. -/
def planeActor {M V : Subgroup G} (d : NaturalOrthogonalAction M V) : Subgroup G :=
  ((RegularWreathProduct.rightHom.comp d.actor).ker).map M.subtype

private theorem coordinate_mem {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) (v : V) :
    (v : G) ∈ d.plane i ↔ d.coordinates v ∈ orthogonalCoordinatePlane i := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- The subgroup acting without permuting planes normalizes each one. -/
theorem planeActor_normalizes {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) : planeActor d ≤ normalizer (d.plane i : Set G) := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  apply le_normalizer_iff.mpr
  rintro m ⟨m₀, hm₀, rfl⟩ v hv
  let v₀ : V := ⟨v, d.plane_le i hv⟩
  let w := V.normalizerMonoidHom ⟨m₀, d.normalizes m₀.property⟩ v₀
  change (w : G) ∈ d.plane i
  rw [coordinate_mem]
  change d.coordinates (V.normalizerMonoidHom _ v₀) ∈ _
  rw [d.compatible]
  intro j hj
  change (d.actor m₀).left j • d.coordinates v₀ ((d.actor m₀).right⁻¹ * j) = 1
  have hm : (d.actor m₀).right = 1 := hm₀
  rw [hm, inv_one, one_mul, ((coordinate_mem d i v₀).mp hv) j hj, smul_one]

/-- Lift the literal SL₂(2) transitivity to a subgroup of M normalizing the plane. -/
theorem planeActor_transitive {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) (x y : G)
    (hx : x ∈ d.plane i) (hx1 : x ≠ 1) (hy : y ∈ d.plane i) (hy1 : y ≠ 1) :
    ∃ m : planeActor d, (MulAut.conj (m : G)) x = y := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  let x₀ : V := ⟨x, d.plane_le i hx⟩
  let y₀ : V := ⟨y, d.plane_le i hy⟩
  have hxi := (coordinate_mem d i x₀).mp hx
  have hyi := (coordinate_mem d i y₀).mp hy
  have nonzero (v : V) (hv : d.coordinates v ∈ orthogonalCoordinatePlane i)
      (hv1 : (v : G) ≠ 1) : (d.coordinates v i).toAdd ≠ 0 := by
    intro he
    have he' : d.coordinates v i = 1 := he
    have hv' : d.coordinates v = 1 := by
      funext j
      by_cases hj : j = i
      · simpa [hj] using he'
      · exact hv j hj
    exact hv1 (congrArg Subtype.val (d.coordinates.injective
      (hv'.trans d.coordinates.map_one.symm)))
  obtain ⟨g, hg⟩ := Matrix.SL2.exists_mulVec_eq (ZMod 2)
    (d.coordinates x₀ i).toAdd (d.coordinates y₀ i).toAdd
    (nonzero x₀ hxi hx1) (nonzero y₀ hyi hy1)
  let a : OrthogonalActor := ⟨fun _ => g, 1⟩
  obtain ⟨m, hm⟩ := d.onto a
  have hmJ : (m : G) ∈ planeActor d := by
    refine mem_map.mpr ⟨m, ?_, rfl⟩
    change (d.actor m).right = 1
    rw [hm]
  refine ⟨⟨m, hmJ⟩, ?_⟩
  have hxy : a • d.coordinates x₀ = d.coordinates y₀ := by
    funext j
    change g • d.coordinates x₀ (1⁻¹ * j) = d.coordinates y₀ j
    rw [inv_one, one_mul]
    by_cases hj : j = i
    · subst j
      exact congrArg Multiplicative.ofAdd hg
    · rw [hxi j hj, hyi j hj, smul_one]
  have hc := d.compatible m x₀
  rw [hm, hxy] at hc
  exact congrArg Subtype.val (d.coordinates.injective hc)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
