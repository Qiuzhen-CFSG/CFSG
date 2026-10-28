module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion.LocalCore
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Planes
public import Theory.GroupTheory.WreathTwoResidual

/-!
# Detecting a normal Sylow core on both definite planes

A noncentral subgroup D normal in T has nontrivial image under the actual
natural orthogonal action. Surjectivity makes the image of T Sylow in the
literal wreath actor. The checked dihedral Sylow calculation supplies an
element of the image of D inverting the entire cubic residual.

A cubic element supported in one coordinate shows that this inverter fixes
the two plane indices and has a nonidentity matrix in each coordinate.
Faithfulness of the binary-plane matrix action therefore makes it nontrivial
on each plane. The compatible vector embedding transports these facts to
normalizers and centralizers for actual conjugation in G. Lifting the inverter
to D gives the desired witness in D ∩ N_T(V₁).

This discharges the orthogonal detection premise of the unitary exclusion;
it does not require an additional hypothesis about the intersection core.
The normal Sylow calculation is reused from `WreathTwoResidual`, whose proof
uses the concrete `wreathTwoDihedralHom` and Sylow conjugacy.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the definite-plane
decomposition and normal-core argument on printed pp.1121–1122, especially
15.3.7, and their use in the unitary branch of 15.3.40 on printed p.1138.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03
namespace RankTwo.RankOnePlane.UnitaryExclusion.OrthogonalCore

private def cubic : OrthogonalPlaneActor := ⟨!![0, 1; 1, 1], by decide⟩

private theorem cubic_cube : cubic ^ 3 = 1 := by decide +kernel
private theorem cubic_ne_one : cubic ≠ 1 := by decide +kernel
private theorem cubic_ne_inv : cubic ≠ cubic⁻¹ := by decide +kernel

private def cubicAt (i : OrthogonalPlaneIndex) : OrthogonalActor :=
  ⟨fun j => if j = i then cubic else 1, 1⟩

private theorem cubicAt_mem_residual (i : OrthogonalPlaneIndex) :
    cubicAt i ∈ pResidual 2 OrthogonalActor := by
  apply mem_pResidual_of_orderOf_coprime
  apply (by decide : Nat.Coprime 2 3).of_dvd_right
  apply orderOf_dvd_of_pow_eq_one
  apply RegularWreathProduct.ext
  · funext j
    by_cases hj : j = i
    · simpa [pow_succ, cubicAt, hj] using cubic_cube
    · simp [pow_succ, cubicAt, hj]
  · simp [pow_succ, cubicAt]

/-- Inverting the cubic base fixes the plane indices and acts nontrivially
on each plane. This uses the literal wreath multiplication. -/
theorem inverter_coordinates (r : OrthogonalActor)
    (hr : ∀ x ∈ pResidual 2 OrthogonalActor, r * x * r⁻¹ = x⁻¹) :
    r.right = 1 ∧ ∀ i, r.left i ≠ 1 := by
  have hconj (i j : OrthogonalPlaneIndex) :
      (r * cubicAt i * r⁻¹).left j =
        r.left j * (cubicAt i).left (r.right⁻¹ * j) * (r.left j)⁻¹ := by
    simp [cubicAt]
  have hshift : r.right = 1 := by
    by_contra hne
    have h := congrArg (fun a : OrthogonalActor => a.left r.right)
      (hr (cubicAt 1) (cubicAt_mem_residual 1))
    rw [hconj] at h
    have he : r.left r.right * cubic * (r.left r.right)⁻¹ = 1 := by
      simpa [cubicAt, hne] using h
    have he' : cubic = 1 := by
      apply mul_left_cancel (a := r.left r.right)
      simpa only [one_mul, mul_one] using mul_inv_eq_iff_eq_mul.mp he
    exact cubic_ne_one he'
  refine ⟨hshift, ?_⟩
  intro i hi
  have h := congrArg (fun a : OrthogonalActor => a.left i)
    (hr (cubicAt i) (cubicAt_mem_residual i))
  rw [hconj] at h
  exact cubic_ne_inv (by simpa [cubicAt, hshift, hi] using h)

open OrthogonalGeometry
local instance : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector :=
  FourGroupMatrixCoordinates.naturalAction
local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction

private theorem left_eq_one_of_pointwise (r : OrthogonalActor)
    (hr : r.right = 1) (i : OrthogonalPlaneIndex)
    (hf : r ∈ pointwise (orthogonalCoordinatePlane i)) : r.left i = 1 := by
  let _ := FourGroupMatrixCoordinates.naturalAction_faithful
  apply FaithfulSMul.eq_of_smul_eq_smul (α := OrthogonalPlaneVector)
  intro u
  let w : OrthogonalVector := fun j => if j = i then u else 1
  have hw : w ∈ orthogonalCoordinatePlane i := fun j hj => if_neg hj
  have he := congrFun (hf w hw) i
  change r.left i • w (r.right⁻¹ * i) = w i at he
  simpa [hr, w] using he

/-- A nontrivial normal subgroup of the actual Sylow actor contains an
actor preserving both definite planes and moving each of them. -/
theorem exists_plane_moving_actor (P : Sylow 2 OrthogonalActor)
    (D : Subgroup OrthogonalActor) (hDP : D ≤ (P : Subgroup OrthogonalActor))
    (hPD : (P : Subgroup OrthogonalActor) ≤ normalizer (D : Set OrthogonalActor))
    (hD : D ≠ ⊥) :
    ∃ r ∈ D, (∀ j, r ∈ setwise (orthogonalCoordinatePlane j)) ∧
      ∀ i, r ∉ pointwise (orthogonalCoordinatePlane i) := by
  obtain ⟨r, hrD, _, hr⟩ :=
    Theory.GroupTheory.WreathTwoResidual.exists_normal_sylow_inverter P D hDP hPD hD
  obtain ⟨hshift, hleft⟩ := inverter_coordinates r hr
  exact ⟨r, hrD, fun j => (mem_setwise_plane_iff r j).mpr hshift,
    fun i hi => hleft i (left_eq_one_of_pointwise r hshift i hi)⟩

end RankTwo.RankOnePlane.UnitaryExclusion.OrthogonalCore

namespace NaturalOrthogonalAction
open OrthogonalGeometry RankTwo.RankOnePlane.UnitaryExclusion.OrthogonalCore
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- A noncentral normal subgroup of a Sylow group acts nontrivially on every
definite plane even after intersection with either plane stabilizer. -/
theorem normal_sylow_inf_planeStabilizer_not_le_centralizer
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (D : Subgroup G)
    (hDT : D ≤ (T : Subgroup G)) (hTD : (T : Subgroup G) ≤ normalizer (D : Set G))
    (hD : ¬ D ≤ centralizer (V : Set G)) (i j : OrthogonalPlaneIndex) :
    ¬ D ⊓ planeStabilizer T (d.plane j) ≤ centralizer (d.plane i : Set G) := by
  have hle : d.image D ≤ (d.sylowImage T hTM : Subgroup OrthogonalActor) :=
    map_mono (comap_mono hDT)
  have hnorm : (d.sylowImage T hTM : Subgroup OrthogonalActor) ≤
      normalizer (d.image D : Set OrthogonalActor) :=
    (map_mono ((comap_mono hTD).trans
      (le_normalizer_comap M.subtype))).trans (le_normalizer_map d.actor)
  have hne : d.image D ≠ ⊥ := by
    exact fun h => hD ((d.image_eq_bot_iff (hDT.trans hTM)).mp h)
  obtain ⟨r, hr, hs, hn⟩ := exists_plane_moving_actor (d.sylowImage T hTM)
    (d.image D) hle hnorm hne
  obtain ⟨m, hm, rfl⟩ := hr
  have hmN : (m : G) ∈ normalizer (d.plane j : Set G) := by
    have he := d.plane_normalizer_eq_comap j
    exact (show m ∈ (normalizer (d.plane j : Set G)).subgroupOf M from
      he ▸ hs j)
  intro hc
  have hmC : (m : G) ∈ centralizer (d.plane i : Set G) :=
    hc ⟨hm, hDT hm, hmN⟩
  apply hn i
  have he := d.centralizer_map_eq_comap (orthogonalCoordinatePlane i)
  rw [← d.plane_eq_map] at he
  exact (show m ∈ (pointwise (orthogonalCoordinatePlane i)).comap d.actor from
    he ▸ hmC)

end NaturalOrthogonalAction

namespace RankTwo.RankOnePlane.UnitaryExclusion
variable {G : Type*} [Group G] [Finite G]

/-- The orthogonal detection premise in `exclusion_of_core_calculations`,
with the actual source stabilizer `S = N_T(V₁)`. -/
theorem normal_sylow_core_detects_plane (d : CharacteristicTwo.LocalData G)
    (i : OrthogonalPlaneIndex) (D : Subgroup G)
    (hDT : D ≤ (d.T : Subgroup G))
    (hTD : (d.T : Subgroup G) ≤ normalizer (D : Set G))
    (hD : ¬ D ≤ centralizer (d.V : Set G)) :
    ¬ D ⊓ d.S ≤ centralizer (d.action.plane i : Set G) :=
  d.action.normal_sylow_inf_planeStabilizer_not_le_centralizer d.T d.sylow_le
    D hDT hTD hD i 1

end RankTwo.RankOnePlane.UnitaryExclusion
end CFSG.Quasithin.Chapter15.Section03

end
