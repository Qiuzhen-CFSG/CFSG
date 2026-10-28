module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification.Coordinates
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification.RootPlane
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.PlaneGeometry

/-!
# Simultaneous root-plane coordinates

An arbitrary F₄-linear change of the two root parameters is realized by
GL₃ conjugation: it fixes the image line and acts contragrediently on the
two complementary natural coordinates. This gives actual equivariant
markings for every binary parameter space of dimension at least three,
using the full field line and independent vector in `PlaneGeometry`.

Source: Aschbacher--Smith, proof of 13.8.20, printed p.955 (PDF p.972).
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification
open Matrix

/-- Coordinate covectors for the two root parameters. -/
def pairDualEquiv : (F × F) ≃ₗ[F] Module.Dual F (F × F) :=
  (((LinearEquiv.finTwoArrow F F).symm.trans (dotProductEquiv F (Fin 2))).trans
    (LinearEquiv.finTwoArrow F F).symm.dualMap)

lemma pairDualEquiv_apply (p x : F × F) :
    pairDualEquiv p x = p.1 * x.1 + p.2 * x.2 := by
  change (fun i : Fin 2 => ![p.1, p.2] i) ⬝ᵥ ![x.1, x.2] = _
  simp [dotProduct, Fin.sum_univ_two]

/-- Transpose with respect to the standard nondegenerate pairing. -/
def pairTranspose (e : (F × F) ≃ₗ[F] (F × F)) : (F × F) ≃ₗ[F] (F × F) :=
  (pairDualEquiv.trans e.dualMap).trans pairDualEquiv.symm

lemma pairTranspose_pair (e : (F × F) ≃ₗ[F] (F × F)) (p x : F × F) :
    p.1 * (pairTranspose e x).1 + p.2 * (pairTranspose e x).2 =
      (e p).1 * x.1 + (e p).2 * x.2 := by
  have h : pairDualEquiv (pairTranspose e x) p = pairDualEquiv x (e p) := by
    simp only [pairTranspose, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.dualMap_apply]
  simpa only [pairDualEquiv_apply, mul_comm] using h

/-- Separate the image line from its two complementary coordinates. -/
def tripleEquiv : W ≃ₗ[F] (F × (F × F)) where
  toFun w := (w 0, (w 1, w 2))
  invFun w := ![w.1, w.2.1, w.2.2]
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv w := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Realize an arbitrary GL₂ parameter change by GL₃ conjugation. -/
def parameterChange (e : (F × F) ≃ₗ[F] (F × F)) : W ≃ₗ[F] W :=
  (tripleEquiv.trans ((LinearEquiv.refl F F).prodCongr (pairTranspose e).symm)).trans
    tripleEquiv.symm

lemma parameterChange_axis (e : (F × F) ≃ₗ[F] (F × F)) :
    parameterChange e ![1, 0, 0] = ![1, 0, 0] := by
  change ![1, ((pairTranspose e).symm (0, 0)).1,
    ((pairTranspose e).symm (0, 0)).2] = _
  have h := (pairTranspose e).symm.map_zero
  change (pairTranspose e).symm (0, 0) = (0, 0) at h
  rw [h]

lemma parameterChange_symm_tail (e : (F × F) ≃ₗ[F] (F × F)) (w : W) :
    ((parameterChange e).symm w 1, (parameterChange e).symm w 2) =
      pairTranspose e (w 1, w 2) := rfl

lemma plane_natural (p : F × F) (w : W) :
    (plane p).val.mulVec w =
      w + (p.1 * w 1 + p.2 * w 2) • ![1, 0, 0] := by
  funext i
  fin_cases i <;> simp [plane, Matrix.mulVec, dotProduct, Fin.sum_univ_three, add_assoc]

lemma coordinateAut_plane (e : (F × F) ≃ₗ[F] (F × F)) (p : F × F) :
    coordinateAut (parameterChange e) (plane p) = plane (e p) := by
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  change (coordinateAut (parameterChange e) (plane p)).val.mulVec w =
    (plane (e p)).val.mulVec w
  rw [coordinateAut_natural, plane_natural, map_add, map_smul,
    LinearEquiv.apply_symm_apply, parameterChange_axis, plane_natural]
  have h := pairTranspose_pair e p (w 1, w 2)
  rw [← parameterChange_symm_tail] at h
  rw [h]

/-- A parameter change acts on the literal subgroup, not just its family label. -/
lemma planeActor_map (e : (F × F) ≃ₗ[F] (F × F))
    (D : Submodule (ZMod 2) (F × F)) :
    (planeActor D).map (coordinateAut (parameterChange e)).toMonoidHom =
      planeActor (D.map (e.restrictScalars (ZMod 2)).toLinearMap) := by
  ext g
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨e p, ⟨p, hp, rfl⟩, (coordinateAut_plane e p).symm⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨plane p, ⟨p, hp, rfl⟩, coordinateAut_plane e p⟩

/-- Every three-dimensional binary parameter space supplies the simultaneous
full-root and independent-root marking required by the source argument. -/
theorem planeActor_marking (D : Submodule (ZMod 2) (F × F))
    (hD : 3 ≤ Module.finrank (ZMod 2) D) :
    ∃ m : LinearMarking representation,
      (∀ a : F, m.actor (root a) ∈ planeActor D) ∧
        m.actor (secondRoot 1) ∈ planeActor D := by
  obtain ⟨e, he, he'⟩ := exists_plane_coordinates D hD
  refine ⟨coordinateMarking (parameterChange e), ?_, ?_⟩
  · intro a
    change (coordinateAut (parameterChange e)).symm (root a) ∈ planeActor D
    have h : (coordinateAut (parameterChange e)).symm (root a) =
        plane (e.symm (0, a)) := by
      apply (coordinateAut (parameterChange e)).injective
      rw [MulEquiv.apply_symm_apply, coordinateAut_plane, e.apply_symm_apply, plane_root]
    rw [h]
    exact (mem_planeActor D _).mpr (he a)
  · change (coordinateAut (parameterChange e)).symm (secondRoot 1) ∈ planeActor D
    have h : (coordinateAut (parameterChange e)).symm (secondRoot 1) =
        plane (e.symm (1, 0)) := by
      apply (coordinateAut (parameterChange e)).injective
      rw [MulEquiv.apply_symm_apply, coordinateAut_plane, e.apply_symm_apply, plane_secondRoot]
    rw [h]
    exact (mem_planeActor D _).mpr he'

end Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification
