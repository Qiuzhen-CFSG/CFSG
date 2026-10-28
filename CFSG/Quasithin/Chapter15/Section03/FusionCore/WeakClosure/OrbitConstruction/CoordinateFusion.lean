module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.OrbitConstruction.CoordinateOrbits

/-!
# Fusion to a plane vector or a Sylow-fixed vector

The literal wreath coordinates have two nonzero orbits, distinguished by the
binary quadratic value. Every nonidentity vector in one coordinate plane has
value one. A vector fixed by a full Sylow two-subgroup has value zero because
the Sylow image contains an actor interchanging the planes. Surjectivity and
compatibility of the given action lift both coordinate orbits to conjugacy
in the original ambient group.

Source: Aschbacher–Smith, the natural O₄⁺(2) geometry in 15.3.38,
printed pp.1136–1137. The application is the involution fusion of the actual
four-cover in `DiagonalOuter.CoverReduction.Assembly.InvolutionFusion`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore
attribute [local instance] orthogonalAction

private theorem coordinate_plane_value : ∀ (i : OrthogonalPlaneIndex) (v : OrthogonalVector),
    v ∈ orthogonalCoordinatePlane i → v ≠ 1 → orthogonalCoordinateValue v = 1 := by
  change ∀ (i : OrthogonalPlaneIndex) (v : OrthogonalVector),
    (∀ j, j ≠ i → v j = 1) → v ≠ 1 → orthogonalCoordinateValue v = 1
  decide +kernel

private theorem coordinate_conjugacy {G : Type*} [Group G] {M V : Subgroup G}
    (a : CFSG.Quasithin.Chapter15.Section03.NaturalOrthogonalAction M V) (x y : V) (hx : x ≠ 1) (hy : y ≠ 1)
    (hq : orthogonalCoordinateValue (a.coordinates x) =
      orthogonalCoordinateValue (a.coordinates y)) : IsConj (x : G) (y : G) := by
  have hne (u : V) (hu : u ≠ 1) : a.coordinates u ≠ 1 := by
    intro he
    exact hu (a.coordinates.injective (he.trans (map_one _).symm))
  obtain ⟨g, hg⟩ := coordinate_orbit _ _ (hne x hx) (hne y hy) hq
  obtain ⟨m, hm⟩ := a.onto g
  refine isConj_iff.mpr ⟨(m : G), ?_⟩
  have he := a.compatible m x
  rw [hm, hg] at he
  exact congrArg Subtype.val (a.coordinates.injective he)

private theorem coordinate_value_fixed_sylow {G : Type*} [Group G] [Finite G]
    {M V : Subgroup G} (a : CFSG.Quasithin.Chapter15.Section03.NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (v : V) (hv : (v : G) ∈ fixedPlane V T) :
    orthogonalCoordinateValue (a.coordinates v) = 0 := by
  have hright := OrthogonalGeometry.sylow_right_image (a.sylowImage T hTM)
  have hmem : Multiplicative.ofAdd (1 : ZMod 2) ∈
      (a.image T).map
        (RegularWreathProduct.rightHom : OrthogonalActor →* OrthogonalPlaneIndex) := by
    rw [← a.coe_sylowImage T hTM, hright]
    exact mem_top _
  obtain ⟨g, hg, hgr⟩ := hmem
  have hfixed := hv
  rw [a.fixedPlane_eq_map hTM] at hfixed
  obtain ⟨w, hw, hwv⟩ := hfixed
  have hcoord : a.coordinates v = w := by
    apply a.coordinates.symm.injective
    rw [a.coordinates.symm_apply_apply]
    exact Subtype.ext hwv.symm
  rw [hcoord]
  apply coordinate_singular_of_swap_fixed g w ?_ (hw g hg)
  change g.right = Multiplicative.ofAdd (1 : ZMod 2) at hgr
  rw [hgr]
  decide

/-- The two literal coordinate orbits give ambient fusion to a marked plane
representative and a nonidentity Sylow-fixed vector. -/
theorem coordinate_involution_fusion {G : Type*} [Group G] [Finite G]
    {M V : Subgroup G} (a : CFSG.Quasithin.Chapter15.Section03.NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (i : OrthogonalPlaneIndex) (v z : G) (hv : v ∈ a.plane i) (hv1 : v ≠ 1)
    (hz : z ∈ fixedPlane V T) (hz1 : z ≠ 1)
    (x : G) (hx : x ∈ V) (hx1 : x ≠ 1) : IsConj x v ∨ IsConj x z := by
  have hvV : v ∈ V := a.plane_le i hv
  let vV : V := ⟨v, hvV⟩
  let zV : V := ⟨z, hz.1⟩
  let xV : V := ⟨x, hx⟩
  have hvcoord : a.coordinates vV ∈ orthogonalCoordinatePlane i := by
    obtain ⟨y, hy, he⟩ := hv
    have he' : y = vV := Subtype.ext he
    change a.coordinates y ∈ orthogonalCoordinatePlane i at hy
    simpa only [← he'] using hy
  have hn (u : G) (hu : u ∈ V) (hne : u ≠ 1) : (⟨u, hu⟩ : V) ≠ 1 := by
    intro he
    exact hne (congrArg Subtype.val he)
  have hvq : orthogonalCoordinateValue (a.coordinates vV) = 1 :=
    coordinate_plane_value i _ hvcoord (by
      intro he
      exact hn v hvV hv1 (a.coordinates.injective (he.trans a.coordinates.map_one.symm)))
  have hzq : orthogonalCoordinateValue (a.coordinates zV) = 0 :=
    coordinate_value_fixed_sylow a T hTM zV hz
  have hq : orthogonalCoordinateValue (a.coordinates xV) = 0 ∨
      orthogonalCoordinateValue (a.coordinates xV) = 1 := by
    exact (show ∀ t : ZMod 2, t = 0 ∨ t = 1 from by decide) _
  rcases hq with hq | hq
  · exact Or.inr (coordinate_conjugacy a xV zV (hn x hx hx1) (hn z hz.1 hz1)
      (hq.trans hzq.symm))
  · exact Or.inl (coordinate_conjugacy a xV vV (hn x hx hx1) (hn v hvV hv1)
      (hq.trans hvq.symm))

end CFSG.Quasithin.Chapter15.Section03.FusionCore
