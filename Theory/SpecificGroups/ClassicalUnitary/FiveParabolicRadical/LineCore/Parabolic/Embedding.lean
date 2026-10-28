module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Matrices
public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag

/-!
# A faithful unipotent subgroup in the unitary-five line parabolic

Conjugating the Witt unipotents gives matrices independent of the trace-one
basis parameter. They preserve the identity form, fix the chosen line, and
act trivially on its perpendicular quotient. Their projective images are
faithful and lie in the flag overlap. The resulting subgroup is isomorphic
to the full coordinate group. Normality and identification with the radical
of the entire parabolic still require the separate block decomposition.

The final two formulas express the original flag in the supplied Witt basis.
Source: the classical unitary calculation in Aschbacher--Smith,
F.1.11--12(7), printed pp.262--264 of `refs/quasithin.pdf`.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

def ambientMatrix (u : Coord J) : Matrix (Fin 5) (Fin 5) F :=
  !![1 + u.scalar,u.scalar,J.conj (u.vector 0),J.conj (u.vector 1),J.conj (u.vector 2);
     u.scalar,1 + u.scalar,J.conj (u.vector 0),J.conj (u.vector 1),J.conj (u.vector 2);
     u.vector 0,u.vector 0,1,0,0;
     u.vector 1,u.vector 1,0,1,0;
     u.vector 2,u.vector 2,0,0,1]

theorem ambientMatrix_eq (c : F) (u : Coord J) :
    ambientMatrix J u = wittBasisMatrix c * unipotentMatrix J u * wittBasisInverse c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientMatrix, wittBasisMatrix, wittBasisInverse, unipotentMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero]

def ambientGL : Coord J →* GL (Fin 5) F :=
  (MulAut.conj (wittBasisGL (0 : F))).toMonoidHom.comp (unipotentGL J)

theorem ambientGL_val (u : Coord J) :
    (ambientGL J u : Matrix (Fin 5) (Fin 5) F) = ambientMatrix J u :=
  (ambientMatrix_eq J 0 u).symm

theorem ambientGL_eq (c : F) (u : Coord J) :
    ambientGL J u = wittBasisGL c * unipotentGL J u * (wittBasisGL c)⁻¹ :=
  Units.ext ((ambientGL_val J u).trans (ambientMatrix_eq J c u))

theorem ambientGL_injective : Function.Injective (ambientGL J) :=
  (MulAut.conj (wittBasisGL (0 : F))).injective.comp (unipotentGL_injective J)

set_option maxRecDepth 2048 in
theorem ambientGL_det (u : Coord J) : Matrix.GeneralLinearGroup.det (ambientGL J u) = 1 := by
  rw [ambientGL_eq J 0, map_mul, map_mul, map_inv]
  have hu : Matrix.GeneralLinearGroup.det (unipotentGL J u) = 1 :=
    Units.ext (unipotentMatrix_det J u)
  rw [hu, mul_one, mul_inv_cancel]

theorem ambientMatrix_preserves (u : Coord J) :
    J.conjTranspose (ambientMatrix J u) * ambientMatrix J u = 1 := by
  have hσ (a : F) := J.conj_involutive a
  have hu := u.trace_eq
  simp [pairing, Fin.sum_univ_succ] at hu
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientMatrix, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ, hσ] <;>
    ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  all_goals
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination hu + (J.conj (u.vector 0) * u.vector 0 + J.conj (u.vector 1) * u.vector 1 +
      J.conj (u.vector 2) * u.vector 2) * h2

def toSU (hJ : J.form = 1) : Coord J →* J.specialSubgroup :=
  (ambientGL J).codRestrict _ (by
    intro u
    rw [J.mem_specialSubgroup_iff]
    refine ⟨?_, ambientGL_det J u⟩
    rw [hJ, mul_one, ambientGL_val]
    exact ambientMatrix_preserves J u)

theorem fixes_line (u : Coord J) (v : Fin 5 → F) (hv : v ∈ line F) :
    ambientMatrix J u *ᵥ v = v := by
  change v 1 = v 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 at hv
  ext i
  fin_cases i <;>
    simp [ambientMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      hv.1, hv.2.1, hv.2.2.1, hv.2.2.2] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero]

theorem toSU_fixes_line (hJ : J.form = 1) (u : Coord J)
    (v : Fin 5 → F) (hv : v ∈ line F) :
    linearAction J (toSU J hJ u) v = v := by
  change (ambientGL J u : Matrix (Fin 5) (Fin 5) F) *ᵥ v = v
  rw [ambientGL_val]
  exact fixes_line J u v hv

theorem toSU_mem_stabilizer (hJ : J.form = 1) (u : Coord J) :
    toSU J hJ u ∈ specialStabilizer J (line F) := by
  rw [mem_specialStabilizer_iff]
  intro v
  change linearAction J (toSU J hJ u) v ∈ line F ↔ v ∈ line F
  constructor
  · intro hv
    have he := toSU_fixes_line J hJ u⁻¹ _ hv
    have hi : linearAction J (toSU J hJ u⁻¹)
        (linearAction J (toSU J hJ u) v) = v := by
      rw [map_inv, map_inv]
      exact (linearAction J (toSU J hJ u)).symm_apply_apply v
    rw [hi] at he
    exact he ▸ hv
  · intro hv
    rw [toSU_fixes_line J hJ u v hv]
    exact hv

/-- The unipotents induce the identity on the perpendicular space modulo the line. -/
theorem fixes_perpendicular_quotient (u : Coord J) (v : Fin 5 → F) (hv : v 1 = v 0) :
    ambientMatrix J u *ᵥ v - v ∈ line F := by
  change _ = _ ∧ _ = 0 ∧ _ = 0 ∧ _ = 0
  simp [ambientMatrix, dotProduct, Fin.sum_univ_succ, hv,
    CharTwo.sub_eq_add]
  constructor
  · ring
  · constructor <;> [skip; constructor] <;>
      ring_nf <;> simp [CharTwo.two_eq_zero]

theorem maps_plane (u : Coord J) (v : Fin 5 → F) (hv : v ∈ plane F) :
    ambientMatrix J u *ᵥ v ∈ plane F := by
  have h := fixes_perpendicular_quotient J u v hv.1
  have he := (plane F).add_mem (line_le_plane F h) hv
  simpa only [sub_add_cancel] using he

theorem toSU_mem_planeStabilizer (hJ : J.form = 1) (u : Coord J) :
    toSU J hJ u ∈ specialStabilizer J (plane F) := by
  have hm (x : Coord J) (v : Fin 5 → F) (hv : v ∈ plane F) :
      linearAction J (toSU J hJ x) v ∈ plane F := by
    change (ambientGL J x : Matrix (Fin 5) (Fin 5) F) *ᵥ v ∈ plane F
    rw [ambientGL_val]
    exact maps_plane J x v hv
  rw [mem_specialStabilizer_iff]
  intro v
  change linearAction J (toSU J hJ u) v ∈ plane F ↔ v ∈ plane F
  constructor
  · intro hv
    have he := hm u⁻¹ _ hv
    have hi : linearAction J (toSU J hJ u⁻¹)
        (linearAction J (toSU J hJ u) v) = v := by
      rw [map_inv, map_inv]
      exact (linearAction J (toSU J hJ u)).symm_apply_apply v
    exact hi ▸ he
  · exact hm u v

def toStabilizer (hJ : J.form = 1) : Coord J →* specialStabilizer J (line F) :=
  (toSU J hJ).codRestrict _ (toSU_mem_stabilizer J hJ)

def toParabolic (hJ : J.form = 1) : Coord J →* lineParabolic J :=
  ((project J).subgroupMap (specialStabilizer J (line F))).comp (toStabilizer J hJ)

theorem toParabolic_injective (hJ : J.form = 1) :
    Function.Injective (toParabolic J hJ) := by
  apply (injective_iff_map_eq_one _).mpr
  intro u hu
  have hp : project J (toSU J hJ u) = 1 := congrArg Subtype.val hu
  have hs : Matrix.ProjGenLinGroup.mk (ambientGL J u) = 1 := congrArg Subtype.val hp
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨a, ha⟩ := hs
  have he := congrArg (fun A : GL (Fin 5) F => (A : Matrix (Fin 5) (Fin 5) F) 4 4) ha
  rw [ambientGL_val] at he
  have hav : a.val = 1 := by simpa [ambientMatrix] using he
  have haone : a = 1 := Units.ext hav
  subst a
  have huone : ambientGL J u = 1 := by simpa using ha.symm
  apply ambientGL_injective J
  simpa using huone

def projectiveUnipotent (hJ : J.form = 1) : Subgroup (lineParabolic J) :=
  (toParabolic J hJ).range

noncomputable def coordinatesEquiv (hJ : J.form = 1) :
    Coord J ≃* projectiveUnipotent J hJ :=
  MonoidHom.ofInjective (toParabolic_injective J hJ)

theorem projectiveUnipotent_isPGroup (hJ : J.form = 1) :
    IsPGroup 2 (projectiveUnipotent J hJ) :=
  Coord.isPGroup.of_equiv (coordinatesEquiv J hJ)

theorem projectiveUnipotent_card (hJ : J.form = 1) :
    Nat.card (projectiveUnipotent J hJ) = Nat.card (Coord J) :=
  Nat.card_congr (coordinatesEquiv J hJ).symm.toEquiv

theorem projectiveUnipotent_le_overlap (hJ : J.form = 1) :
    projectiveUnipotent J hJ ≤
      (lineParabolic J ⊓ planeParabolic J).subgroupOf (lineParabolic J) := by
  rintro g ⟨u, rfl⟩
  exact ⟨(toParabolic J hJ u).property,
    ⟨toSU J hJ u, toSU_mem_planeStabilizer J hJ u, rfl⟩⟩

omit [CharP F 2] in
theorem wittBasis_mulVec (c : F) (v : Fin 5 → F) :
    wittBasisMatrix c *ᵥ v =
      ![v 0 + c * v 4, v 0 + (1 + c) * v 4, v 1, v 2, v 3] := by
  ext i
  fin_cases i <;> simp [wittBasisMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

omit [CharP F 2] in
/-- The original line is the first coordinate line in the supplied Witt basis. -/
theorem wittBasis_mem_line_iff (c : F) (v : Fin 5 → F) :
    wittBasisMatrix c *ᵥ v ∈ line F ↔
      v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 := by
  rw [wittBasis_mulVec]
  change (v 0 + (1 + c) * v 4 = v 0 + c * v 4 ∧
    v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0) ↔ _
  constructor
  · rintro ⟨h, h1, h2, h3⟩
    exact ⟨h1, h2, h3, by linear_combination h⟩
  · rintro ⟨h1, h2, h3, h4⟩
    simp [h1, h2, h3, h4]

omit [CharP F 2] in
/-- The flag plane is the first Witt line plus the middle line generated by `(1,1,0)`. -/
theorem wittBasis_mem_plane_iff (c : F) (v : Fin 5 → F) :
    wittBasisMatrix c *ᵥ v ∈ plane F ↔
      v 4 = 0 ∧ v 2 = v 1 ∧ v 3 = 0 := by
  rw [wittBasis_mulVec]
  change (v 0 + (1 + c) * v 4 = v 0 + c * v 4 ∧
    v 2 = v 1 ∧ v 3 = 0) ↔ _
  constructor
  · rintro ⟨h, h2, h3⟩
    exact ⟨by linear_combination h, h2, h3⟩
  · rintro ⟨h4, h2, h3⟩
    simp [h2, h3, h4]

end Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
