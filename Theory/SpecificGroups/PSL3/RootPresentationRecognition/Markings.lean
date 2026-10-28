module
public import Theory.SpecificGroups.PSL3.RootPresentationRecognition.Core
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.BorelOvergroups
public import Theory.SpecificGroups.PSL3.BorelTwoParabolics
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Positive roots and the marked degree-three flag

The three positive root ranges generate the actual upper-unitriangular
subgroup, by its three-entry normal form. An equivalence preserving root
parameters therefore identifies unipotent groups and their full normalizers.
Among maximal proper Borel overgroups, one negative simple-root element
selects each of the point and line parabolics, through the scalar quotient.

Source: Steinberg §6, pp.71–74; DGS, Groups and Graphs, Theorem D, p.224.
-/

@[expose] public noncomputable section
open scoped MatrixGroups
open Theory.SpecificGroups.LinearHigher
open Matrix.PSL3.UniversalProjection.Faithfulness
open Matrix.PSL3.LinearThree Subgroup
namespace Matrix.PSL3.RootPresentationRecognition
variable {F Y : Type*} [Field F] [Group Y]

/-- Positive root closure with the original root indices retained. -/
def positiveClosure (x : Root 3 → F → Y) : Subgroup Y :=
  closure {g | ∃ (r : Root 3) (a : F), r.val.1 < r.val.2 ∧ g = x r a}

/-- The matrix normal form gives the entire concrete unipotent group. -/
theorem positiveClosure_projectiveRoot :
    positiveClosure (projectiveRoot (F := F)) = unipotent F := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro g ⟨⟨⟨i,j⟩,hij⟩,a,hr,rfl⟩
    apply mem_map_of_mem (projection F)
    rw [mem_unipotentSL_iff]
    fin_cases i <;> fin_cases j <;>
      simp_all [matrixRoot, Matrix.SpecialLinearGroup.transvection_coe] <;>
      ext k l <;> fin_cases k <;> fin_cases l <;>
      simp
  · rintro g ⟨u,hu,rfl⟩
    have he : matrixMap (PositiveCollection.normal (u.val 0 1) (u.val 1 2)
        (u.val 0 2)) = u :=
      Subtype.ext ((PositiveCollection.matrix_normal _ _ _).trans
        ((mem_unipotentSL_iff F u).mp hu).symm)
    rw [← he]
    simp only [PositiveCollection.normal, PositiveCollection.x12,
      PositiveCollection.x02, PositiveCollection.x01, map_mul, matrixMap_generator]
    apply mul_mem
    · apply mul_mem
      · exact subset_closure ⟨root 1 2 (by decide), _, by decide, rfl⟩
      · exact subset_closure ⟨root 0 2 (by decide), _, by decide, rfl⟩
    · exact subset_closure ⟨root 0 1 (by decide), _, by decide, rfl⟩

/-- Any root-preserving equivalence maps the specified positive group exactly. -/
theorem map_positiveClosure {x : Root 3 → F → Y} (e : Y ≃* PSL(3,F))
    (he : ∀ r a, e (x r a) = projectiveRoot r a) :
    (positiveClosure x).map e.toMonoidHom = unipotent F := by
  rw [positiveClosure, MonoidHom.map_closure]
  rw [← positiveClosure_projectiveRoot (F := F)]
  congr 1
  ext g
  constructor
  · rintro ⟨y,⟨r,a,hr,rfl⟩,rfl⟩
    exact ⟨r,a,hr,he r a⟩
  · rintro ⟨r,a,hr,rfl⟩
    exact ⟨x r a,⟨r,a,hr,rfl⟩,he r a⟩

/-- Full normalizers recover every torus element of the Borel as well. -/
theorem map_borel [Finite F] [CharP F 2] {x : Root 3 → F → Y}
    (e : Y ≃* PSL(3,F)) (he : ∀ r a, e (x r a) = projectiveRoot r a)
    (U B : Subgroup Y) (hU : positiveClosure x = U) (hB : normalizer (U : Set Y) = B) :
    B.map e.toMonoidHom = borel F := by
  rw [← hB, map_normalizer_eq_of_bijective _ e.bijective, ← hU,
    map_positiveClosure e he, normalizer_unipotent_of_charTwo]

variable [Finite F]

/-- The opposite root 21 survives the scalar quotient outside the line parabolic. -/
theorem root21_not_mem_line :
    projectiveRoot (root (2 : Fin 3) 1 (by decide)) (1 : F) ∉ lineParabolic F := by
  change projection F (matrixRoot (root 2 1 (by decide)) (1 : F)) ∉ lineParabolic F
  rw [← mem_comap, lineParabolic_comap, mem_lineParabolicSL_iff]
  simp [matrixRoot, root, Matrix.SpecialLinearGroup.transvection_coe]

/-- The opposite root 10 survives the scalar quotient outside the point parabolic. -/
theorem root10_not_mem_point :
    projectiveRoot (root (1 : Fin 3) 0 (by decide)) (1 : F) ∉ pointParabolic F := by
  change projection F (matrixRoot (root 1 0 (by decide)) (1 : F)) ∉ pointParabolic F
  rw [← mem_comap, pointParabolic_comap, mem_pointParabolicSL_iff]
  simp [matrixRoot, root, Matrix.SpecialLinearGroup.transvection_coe]

/-- A single marked negative-root element selects the full point parabolic. -/
theorem map_pointParabolic {x : Root 3 → F → Y} (e : Y ≃* PSL(3,F))
    (he : ∀ r a, e (x r a) = projectiveRoot r a) (B P : Subgroup Y)
    (hB : B.map e.toMonoidHom = borel F) (hBP : B ≤ P) (hP : IsCoatom P)
    (h21 : x (root (2 : Fin 3) 1 (by decide)) 1 ∈ P) :
    P.map e.toMonoidHom = pointParabolic F := by
  have hp : IsCoatom (P.map e.toMonoidHom) := (OrderIso.isCoatom_iff e.mapSubgroup P).mpr hP
  have hb : borel F ≤ P.map e.toMonoidHom := hB ▸ map_mono hBP
  have hle : P.map e.toMonoidHom ≤ pointParabolic F := by
    rcases BorelOvergroups.overgroup_borel F _ hb hp.ne_top with h | h
    · exact h
    · exact (root21_not_mem_line (F := F)
        (h (he _ _ ▸ mem_map_of_mem e.toMonoidHom h21))).elim
  exact le_antisymm hle ((isCoatom_iff_ge_of_le.mp hp).2 _
    (projective_parabolics_isCoatom F).1.ne_top hle)

/-- The other marked negative-root element selects the full line parabolic. -/
theorem map_lineParabolic {x : Root 3 → F → Y} (e : Y ≃* PSL(3,F))
    (he : ∀ r a, e (x r a) = projectiveRoot r a) (B P : Subgroup Y)
    (hB : B.map e.toMonoidHom = borel F) (hBP : B ≤ P) (hP : IsCoatom P)
    (h10 : x (root (1 : Fin 3) 0 (by decide)) 1 ∈ P) :
    P.map e.toMonoidHom = lineParabolic F := by
  have hp : IsCoatom (P.map e.toMonoidHom) := (OrderIso.isCoatom_iff e.mapSubgroup P).mpr hP
  have hb : borel F ≤ P.map e.toMonoidHom := hB ▸ map_mono hBP
  have hle : P.map e.toMonoidHom ≤ lineParabolic F := by
    rcases BorelOvergroups.overgroup_borel F _ hb hp.ne_top with h | h
    · exact (root10_not_mem_point (F := F)
        (h (he _ _ ▸ mem_map_of_mem e.toMonoidHom h10))).elim
    · exact h
  exact le_antisymm hle ((isCoatom_iff_ge_of_le.mp hp).2 _
    (projective_parabolics_isCoatom F).2.ne_top hle)
end Matrix.PSL3.RootPresentationRecognition
