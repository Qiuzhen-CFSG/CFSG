module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.OrbitConstruction.CoordinateOrbits
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.OrbitConstruction.WreathComparison
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry
public import Theory.SpecificGroups.OrthogonalFourBinary.PlusTypeCoordinates

/-!
# Constructing compatible orthogonal coordinates and fusion calculations

Nondegeneracy, dimension four and the totally singular plane identify the
given quadratic space with the orthogonal sum of two definite binary planes.
The full isometry action then gives compatible surjective matrix wreath
coordinates and identifies the chosen definite plane with a coordinate plane.

The order-two central subgroup supplies `z`, whose Sylow fixedness makes it
singular. The plane stabilizer fixes a line of order two in the chosen definite
plane; its generator `v` is nonsingular. The coordinate orbit calculation gives
both local conjugacy orbits. The odd index in the local fixed-line centralizer,
together with 15.3.45(3), makes the actual plane stabilizer a Sylow subgroup of
the full ambient centralizer of `v`. Its index in `T` is two.

The final constructor packages both the coordinate comparison and the fusion
calculations using only the given natural orthogonal action, earlier source
inputs and definiteness of the chosen plane. No global fusion-control or
weak-closure-centralization assumption is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122, 15.3.45(3) on p.1140 and the opening proof of 15.3.46 on p.1141.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore
open Subgroup
open scoped IsMulCommutative
attribute [local instance] orthogonalAction

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M V P : Subgroup G} [IsElementaryAbelian 2 V]

/-- The intrinsic plus-type quadratic hypotheses and full action construct
compatible surjective wreath coordinates marking the given definite plane. -/
theorem orthogonalCoordinateModel_nonempty
    (d : NaturalOrthogonalAction M V) (hP : IsDefinitePlane d.form P) :
    Nonempty (OrthogonalCoordinateModel d P) := by
  obtain ⟨e⟩ := OrthogonalFourBinary.nonempty_isometryEquiv_of_plusType
    d.form d.nondegenerate d.dimension d.plusType
  exact orthogonalCoordinateModel_nonempty_of_isometry d hP e

private theorem fixed_line_generator
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (hP : IsDefinitePlane d.form P) (k : OrthogonalCoordinateModel d P) :
    ∃ v : V, v ≠ 1 ∧
      fixedPlane P (planeStabilizer T P) = zpowers (v : G) := by
  obtain ⟨i, hi⟩ := k.plane_eq
  have hc : Nat.card (fixedPlane P (planeStabilizer T P)) = 2 := by
    rw [hi]
    exact k.action.card_plane_fixed_planeStabilizer T h.sylow_le i
  let L := fixedPlane P (planeStabilizer T P)
  have : Nontrivial L := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)
  obtain ⟨v, hv⟩ := exists_ne (1 : L)
  let w : V := ⟨v, hP.1 v.property.1⟩
  have hw : w ≠ 1 := by
    intro he
    have he' : (v : G) = 1 := congrArg (fun x : V => (x : G)) he
    exact hv (Subtype.ext he')
  refine ⟨w, hw, ?_⟩
  have he : zpowers v = ⊤ := zpowers_eq_top_of_prime_card hc hv
  have hm := congrArg (fun K : Subgroup L => K.map L.subtype) he
  rw [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm.symm

private theorem full_centralizer_sylow
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (k : OrthogonalCoordinateModel d P) (v : V)
    (hline : fixedPlane P (planeStabilizer T P) = zpowers (v : G)) :
    ∃ R : Sylow 2 (centralizer ({(v : G)} : Set G)),
      (R : Subgroup (centralizer ({(v : G)} : Set G))).map
        (centralizer ({(v : G)} : Set G)).subtype = planeStabilizer T P := by
  let S := planeStabilizer T P
  let C := centralizer ({(v : G)} : Set G)
  have hC : centralizer (fixedPlane P S : Set G) = C := by
    rw [hline, zpowers_eq_closure, centralizer_closure]
  have hCM : C ≤ M := hC ▸ h.plane_fixed_centralizer
  have hSC : S ≤ C := by
    have hv : (v : G) ∈ fixedPlane P S := hline.symm ▸ mem_zpowers _
    intro s hs
    exact mem_centralizer_singleton_iff.mpr (hv.2 s hs)
  obtain ⟨i, hi⟩ := k.plane_eq
  have hindex : ¬ 2 ∣ S.relIndex C := by
    have hl := k.action.not_dvd_planeStabilizer_centralizer_relIndex T h.sylow_le i
    rw [← hi, hC, inf_eq_right.mpr hCM] at hl
    exact hl
  have hp : IsPGroup 2 S := T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)
  let R : Sylow 2 C := (hp.comap_subtype (K := C)).toSylow hindex
  exact ⟨R, map_subgroupOf_eq_of_le hSC⟩

/-- Construct all orbit and full-centralizer Sylow data after the actual
quadratic/wreath comparison has been established. -/
theorem orthogonalFusionCalculations_of_coordinates
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (hP : IsDefinitePlane d.form P) (k : OrthogonalCoordinateModel d P) :
    Nonempty (OrthogonalFusionCalculations T M V P d.form) := by
  have : Nontrivial (centralInvolutions T) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h.central_order]; decide)
  obtain ⟨z₀, hz₀⟩ := exists_ne (1 : centralInvolutions T)
  have hzfixed : (z₀ : G) ∈ fixedPlane V T := h.central_fixed ▸ z₀.property
  let z : V := ⟨z₀, hzfixed.1⟩
  have hz : z ≠ 1 := by
    intro he
    have he' : (z₀ : G) = 1 := congrArg (fun x : V => (x : G)) he
    exact hz₀ (Subtype.ext he')
  have hzs := k.singular_of_fixedPlane_sylow T h.sylow_le z hzfixed
  obtain ⟨v, hv, hline⟩ := fixed_line_generator d h hP k
  have hvP : (v : G) ∈ P := (hline.symm ▸ mem_zpowers (v : G)).1
  have hvq := hP.2.2 v hvP hv
  obtain ⟨R, hR⟩ := full_centralizer_sylow d h k v hline
  refine ⟨{
    z := z
    z_ne_one := hz
    z_central := z₀.property
    z_singular := hzs
    v := v
    v_ne_one := hv
    fixed_line := hline
    singular_orbit := ?_
    nonsingular_orbit := ?_
    centralizer_sylow := R
    sylow_image := hR
    stabilizer_index := ?_ }⟩
  · intro u hu hq
    exact k.conjugateBy_of_value_eq z u hz hu (hzs.trans hq.symm)
  · intro u hu
    have hu1 : u ≠ 1 := by
      intro he
      apply hu
      simp [he]
    have heq : d.form (Additive.ofMul v) = d.form (Additive.ofMul u) :=
      (show ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b by decide) _ _ hvq hu
    exact k.conjugateBy_of_value_eq v u hv hu1 heq
  · obtain ⟨i, hi⟩ := k.plane_eq
    rw [hi]
    exact k.action.planeStabilizer_index_two T h.sylow_le i

/-- Construct the actual coordinate model together with the two local orbits,
the fixed line, and a Sylow subgroup of the full ambient centralizer whose
image is the plane stabilizer of index two in `T`. -/
theorem orthogonalCoordinateModel_and_fusionCalculations
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (hP : IsDefinitePlane d.form P) :
    Nonempty (OrthogonalCoordinateModel d P ×
      OrthogonalFusionCalculations T M V P d.form) := by
  obtain ⟨k⟩ := orthogonalCoordinateModel_nonempty d hP
  obtain ⟨c⟩ := orthogonalFusionCalculations_of_coordinates d h hP k
  exact ⟨k, c⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore
