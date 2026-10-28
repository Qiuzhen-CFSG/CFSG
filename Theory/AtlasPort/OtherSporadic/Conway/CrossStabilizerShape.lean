/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/CrossStabilizerShape.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechCrossAction
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/CrossStabilizerShape.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem standardCross_axis_mem (a : Omega) : coordinateEight a ∈ crossVectors standardCross := by
  apply (crossVectors_mem _ _).mpr
  refine ⟨coordinateEight_class _ _,?_⟩
  change integerDot (coordinateVector a 8) (coordinateVector a 8) = 64
  rw [integerDot_coordinateVector]; simp [coordinateVector]

theorem standardCross_axis_image (g : LeechIsometryGroup)
    (hg : crossAction g standardCross = standardCross) (a : Omega) :
    ∃ p : Omega × Bit, (g.val (coordinateEight a)).val = eightAxisVector p := by
  have hm : g.val (coordinateEight a) ∈ crossVectors standardCross := by
    rw [← hg,← crossVectors_transport]
    exact Finset.mem_image.mpr ⟨coordinateEight a,standardCross_axis_mem a,rfl⟩
  have hh : (g.val (coordinateEight a)).val ∈ axisEightVectors := by
    rw [← standardCross_vectors]
    exact Finset.mem_image.mpr ⟨g.val (coordinateEight a),hm,rfl⟩
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hh
  exact ⟨p,hp.symm⟩

def standardCrossAxisImage (g : LeechIsometryGroup)
    (hg : crossAction g standardCross = standardCross) (a : Omega) : Omega × Bit :=
  Classical.choose (standardCross_axis_image g hg a)

theorem standardCrossAxisImage_spec (g : LeechIsometryGroup)
    (hg : crossAction g standardCross = standardCross) (a : Omega) :
    (g.val (coordinateEight a)).val = eightAxisVector (standardCrossAxisImage g hg a) :=
  Classical.choose_spec (standardCross_axis_image g hg a)

theorem standardCross_coordinate (g : LeechIsometryGroup)
    (hg : crossAction g standardCross = standardCross) (a : Omega) (x : leech) :
    (g.val x).val (standardCrossAxisImage g hg a).1 =
      if (standardCrossAxisImage g hg a).2 = 0 then x.val a else -x.val a := by
  have hh := g.prop x (coordinateEight a)
  rw [standardCrossAxisImage_spec g hg a] at hh
  change integerDot (g.val x).val (coordinateVector _ _) = integerDot x.val (coordinateVector a 8) at hh
  rw [integerDot_coordinateVector,integerDot_coordinateVector] at hh
  change (g.val x).val _ * (if (standardCrossAxisImage g hg a).2 = 0 then 8 else -8) = x.val a * 8 at hh
  split_ifs at hh ⊢ <;> omega

theorem standardCrossAxisImage_injective (g : LeechIsometryGroup)
    (hg : crossAction g standardCross = standardCross) :
    Function.Injective (fun a => (standardCrossAxisImage g hg a).1) := by
  intro a b hab
  change (standardCrossAxisImage g hg a).1 = (standardCrossAxisImage g hg b).1 at hab
  by_contra hn
  have ha := standardCross_coordinate g hg a (coordinateEight a)
  have hb := standardCross_coordinate g hg b (coordinateEight a)
  rw [hab] at ha
  have hba : b ≠ a := Ne.symm hn
  simp only [coordinateEight,coordinateVector,Pi.single_eq_same] at ha
  simp only [coordinateEight,coordinateVector,Pi.single_apply,hba,ite_false,neg_zero,ite_self] at hb
  rw [hb] at ha
  split_ifs at ha; norm_num at ha

def standardCrossCoordinatePermutation (g : LeechIsometryGroup)
    (hg : crossAction g standardCross = standardCross) : Equiv.Perm Omega :=
  Equiv.ofBijective (fun a => (standardCrossAxisImage g hg a).1)
    ⟨standardCrossAxisImage_injective g hg,
      Finite.surjective_of_injective (standardCrossAxisImage_injective g hg)⟩

def standardCrossSignWord (g : LeechIsometryGroup)
    (hg : crossAction g standardCross = standardCross) : BinaryWord :=
  fun i => (standardCrossAxisImage g hg ((standardCrossCoordinatePermutation g hg).symm i)).2

theorem standardCross_signed_shape (g : LeechIsometryGroup)
    (hg : crossAction g standardCross = standardCross) (x : leech) (i : Omega) :
    (g.val x).val i = if standardCrossSignWord g hg i = 0 then
      x.val ((standardCrossCoordinatePermutation g hg).symm i)
      else -x.val ((standardCrossCoordinatePermutation g hg).symm i) := by
  have h := standardCross_coordinate g hg ((standardCrossCoordinatePermutation g hg).symm i) x
  have he : (standardCrossAxisImage g hg ((standardCrossCoordinatePermutation g hg).symm i)).1 = i :=
    (standardCrossCoordinatePermutation g hg).apply_symm_apply i
  rwa [he] at h

end Atlas.Conway
