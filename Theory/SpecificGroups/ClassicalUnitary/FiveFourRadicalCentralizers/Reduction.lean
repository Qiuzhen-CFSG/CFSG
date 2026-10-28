module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFourScalarKernel
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Embedding
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Matrices

/-!
# Reducing the unitary-five radical centralizers to matrix equations

The scalar kernel of SU₅(4) → PSU₅(4) has order five. A radical element has
fourth power one, so projective commutation lifts to actual commutation.
Fourth-power conjugation is nontrivial on a field of order sixteen; normalizing
an element by its trace supplies the trace-one scalar needed in the matrix
calculations.

We specify the two expected matrix normal forms and prove that every
special-unitary matrix of either form represents an element of the corresponding
concrete projective radical. Unitarity supplies the parameter relations after
removing a fifth-root scalar. The final two theorems reduce the intrinsic
parabolic centralizer bounds to the independent matrix normal-form calculations.
They retain those calculations as explicit premises.

Source: the characteristic-two parabolic calculation supporting
Aschbacher--Smith, *The Classification of Quasithin Groups*, Theorem 0.1.2(1)
and F.1.12(7), printed pp.4 and 263--264 of `refs/quasithin.pdf`.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.RadicalCentralizers
variable {F : Type*} [Field F]
variable (J : HermitianForm 5 F)

/-- Projectively commuting special-unitary matrices commute when one has fourth
power one: their central commutator has order dividing both four and five. -/
theorem commute_of_project_commute_fourth_power [Finite F] (hconj : ∀ x : F, J.conj x = x ^ 4) (hcard : Nat.card F = 16)
    {A B : J.specialSubgroup} (hproj : project J A * project J B = project J B * project J A)
    (hB : B ^ 4 = 1) : A * B = B * A := by
  let C : J.specialSubgroup := (A * B) * (B * A)⁻¹
  have hCker : C ∈ (project J).ker := by
    change project J C = 1
    simp only [C, map_mul, map_inv]
    rw [hproj]
    simp
  have hCcenter : C * B = B * C :=
    (Subgroup.mem_center_iff.mp (project_kernel_le_center J (show C ∈ (project J).ker from hCker)) B).symm
  have hconjC : A * B * A⁻¹ = C * B := by
    dsimp [C]
    group
  have hp := congrArg (fun x : J.specialSubgroup => x ^ 4) hconjC
  have hCBpow : (C * B) ^ 4 = C ^ 4 * B ^ 4 :=
    (show Commute C B from hCcenter).mul_pow 4
  have hleft : (A * B * A⁻¹) ^ 4 = 1 := by
    rw [conj_pow, hB]
    simp
  have hright : (C * B) ^ 4 = C ^ 4 := by
    rw [hCBpow, hB, mul_one]
  have hC4 : C ^ 4 = 1 := by
    exact hright.symm.trans (hp.symm.trans hleft)
  let cK : (project J).ker := ⟨C, hCker⟩
  have hdiv4 : orderOf cK ∣ 4 := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    apply Subtype.ext
    exact hC4
  have hdiv5 : orderOf cK ∣ 5 := by
    have hcardK : Nat.card (project J).ker = 5 := card_project_kernel J hconj hcard
    exact (orderOf_dvd_natCard cK).trans (dvd_of_eq hcardK)
  have hord : orderOf cK = 1 := by
    have : orderOf cK ∣ Nat.gcd 4 5 := Nat.dvd_gcd hdiv4 hdiv5
    norm_num at this ⊢
    exact this
  have hcK : cK = 1 := orderOf_eq_one_iff.mp hord
  have hC : C = 1 := congrArg Subtype.val hcK
  change (A * B) * (B * A)⁻¹ = 1 at hC
  exact eq_of_mul_inv_eq_one hC

/-- Fourth-power conjugation over the field of sixteen elements is nontrivial,
so its trace map attains one. -/
theorem exists_trace_one [Finite F] [CharP F 2] (hconj : ∀ x : F, J.conj x = x ^ 4) (hcard : Nat.card F = 16) :
    ∃ c : F, c + J.conj c = 1 := by
  apply LineCore.exists_trace_one J
  by_contra! h
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have h4 : (u : F) ^ 4 = u := (hconj u).symm.trans (h u)
  have h3 : u ^ 3 = 1 := by
    apply Units.ext
    change (u : F) ^ 3 = 1
    apply mul_right_cancel₀ u.ne_zero
    simpa only [← pow_succ, one_mul] using h4
  have hd : 15 ∣ 3 := by
    have hd := orderOf_dvd_of_pow_eq_one h3
    simpa only [hu, Nat.card_units, hcard] using hd
  norm_num at hd


/-- Scalar matrices plus the rank-one nilpotent supported on the chosen line. -/
def lineCentralMatrix (a b : F) : Matrix (Fin 5) (Fin 5) F :=
  !![a+b,b,0,0,0; b,a+b,0,0,0; 0,0,a,0,0; 0,0,0,a,0; 0,0,0,0,a]

/-- Scalar matrices plus the square-zero maps from the dual plane to the plane. -/
def planeCentralMatrix (a : F) (z : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 5) (Fin 5) F :=
  !![a+z 0 0,z 0 0,z 0 1,z 0 1,0;
     z 0 0,a+z 0 0,z 0 1,z 0 1,0;
     z 1 0,z 1 0,a+z 1 1,z 1 1,0;
     z 1 0,z 1 0,z 1 1,a+z 1 1,0;
     0,0,0,0,a]

private theorem line_norm (hJ : J.form = 1) (A : J.specialSubgroup)
    (a b : F) (hA : A.val.val = lineCentralMatrix a b) : J.conj a * a = 1 := by
  have h := (J.mem_specialSubgroup_iff _).mp A.property |>.1
  rw [hJ, mul_one, hA] at h
  have he := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M 4 4) h
  simpa [lineCentralMatrix, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ] using he

private theorem plane_norm (hJ : J.form = 1) (A : J.specialSubgroup)
    (a : F) (z : Matrix (Fin 2) (Fin 2) F)
    (hA : A.val.val = planeCentralMatrix a z) : J.conj a * a = 1 := by
  have h := (J.mem_specialSubgroup_iff _).mp A.property |>.1
  rw [hJ, mul_one, hA] at h
  have he := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M 4 4) h
  simpa [planeCentralMatrix, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ] using he

private theorem line_parameter [CharP F 2] (hJ : J.form = 1) (B : J.specialSubgroup)
    (b : F) (hB : B.val.val = lineCentralMatrix 1 b) :
    ∃ v : LineCore.Coord J, LineCore.Parabolic.toSU J hJ v = B := by
  have h := (J.mem_specialSubgroup_iff _).mp B.property |>.1
  rw [hJ, mul_one, hB] at h
  have he := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M 0 1) h
  simp [lineCentralMatrix, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ] at he
  have hb : b + J.conj b = 0 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination he - (J.conj b * b) * h2
  let v : LineCore.Coord J := ⟨0, b, by simpa using hb⟩
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change (LineCore.Parabolic.ambientGL J v).val = B.val.val
  rw [LineCore.Parabolic.ambientGL_val, hB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LineCore.Parabolic.ambientMatrix, lineCentralMatrix, v]

private theorem plane_parameter [CharP F 2] (hJ : J.form = 1) (B : J.specialSubgroup)
    (z : Matrix (Fin 2) (Fin 2) F) (hB : B.val.val = planeCentralMatrix 1 z) :
    ∃ v : PlaneCore.Parameters J, PlaneCore.Parameters.toSU hJ v = B := by
  have h := (J.mem_specialSubgroup_iff _).mp B.property |>.1
  rw [hJ, mul_one, hB] at h
  have he (i j : Fin 5) := congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j) h
  have h00 := he 0 1
  have h01 := he 0 2
  have h10 := he 2 0
  have h11 := he 2 3
  simp [planeCentralMatrix, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ] at h00 h01 h10 h11
  have hz : ∀ i j, z i j + J.conj (z j i) = 0 := by
    intro i j
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    fin_cases i <;> fin_cases j
    · change z 0 0 + J.conj (z 0 0) = 0
      linear_combination h00 - (J.conj (z 0 0) * z 0 0 + J.conj (z 1 0) * z 1 0) * h2
    · change z 0 1 + J.conj (z 1 0) = 0
      linear_combination h01 - (J.conj (z 0 0) * z 0 1 + J.conj (z 1 0) * z 1 1) * h2
    · change z 1 0 + J.conj (z 0 1) = 0
      linear_combination h10 - (J.conj (z 0 1) * z 0 0 + J.conj (z 1 1) * z 1 0) * h2
    · change z 1 1 + J.conj (z 1 1) = 0
      linear_combination h11 - (J.conj (z 0 1) * z 0 1 + J.conj (z 1 1) * z 1 1) * h2
  let v : PlaneCore.Parameters J := ⟨0, z, by simpa using hz⟩
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change (PlaneCore.Parameters.ambientGL v).val = B.val.val
  rw [PlaneCore.Parameters.ambientGL_val, hB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PlaneCore.Parameters.ambientMatrix, planeCentralMatrix, v]


private theorem exists_normalized (hconj : ∀ x : F, J.conj x = x ^ 4)
    (A : J.specialSubgroup) (a : F) (ha : J.conj a * a = 1) :
    ∃ B : J.specialSubgroup, project J B = project J A ∧
      B.val.val = a⁻¹ • A.val.val := by
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha
  let u : Fˣ := Units.mk0 a ha0
  have hu : u ∈ rootsOfUnity 5 F := by
    apply (mem_rootsOfUnity' 5 u).mpr
    change a ^ 5 = 1
    simpa only [hconj, pow_succ] using ha
  let k : J.specialSubgroup := (scalarToKernel J hconj ⟨u, hu⟩).val
  have hk : project J k = 1 := (scalarToKernel J hconj ⟨u, hu⟩).property
  refine ⟨k⁻¹ * A, ?_, ?_⟩
  · rw [map_mul, map_inv, hk, inv_one, one_mul]
  · change ((GeneralLinearGroup.scalar (Fin 5) u)⁻¹ * A.val).val = a⁻¹ • A.val.val
    rw [← map_inv, Units.val_mul, GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar, Matrix.diagonal_mul, u]

private theorem line_image_of_shape [CharP F 2] (hJ : J.form = 1)
    (hconj : ∀ x : F, J.conj x = x ^ 4)
    (A : J.specialSubgroup) (a b : F) (hA : A.val.val = lineCentralMatrix a b) :
    ∃ v : LineCore.Coord J, project J (LineCore.Parabolic.toSU J hJ v) = project J A := by
  obtain ⟨B, hproj, hB⟩ := exists_normalized J hconj A a (line_norm J hJ A a b hA)
  have ha0 : a ≠ 0 := by
    have h := line_norm J hJ A a b hA
    intro he
    simp [he] at h
  have hB' : B.val.val = lineCentralMatrix 1 (a⁻¹ * b) := by
    rw [hB, hA]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lineCentralMatrix, mul_add, ha0]
  obtain ⟨v, hv⟩ := line_parameter J hJ B (a⁻¹ * b) hB'
  exact ⟨v, by rw [hv]; exact hproj⟩

private theorem plane_image_of_shape [CharP F 2] (hJ : J.form = 1)
    (hconj : ∀ x : F, J.conj x = x ^ 4)
    (A : J.specialSubgroup) (a : F) (z : Matrix (Fin 2) (Fin 2) F)
    (hA : A.val.val = planeCentralMatrix a z) :
    ∃ v : PlaneCore.Parameters J, project J (PlaneCore.Parameters.toSU hJ v) = project J A := by
  obtain ⟨B, hproj, hB⟩ := exists_normalized J hconj A a (plane_norm J hJ A a z hA)
  have ha0 : a ≠ 0 := by
    have h := plane_norm J hJ A a z hA
    intro he
    simp [he] at h
  have hB' : B.val.val = planeCentralMatrix 1 (a⁻¹ • z) := by
    rw [hB, hA]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeCentralMatrix, mul_add, ha0]
  obtain ⟨v, hv⟩ := plane_parameter J hJ B (a⁻¹ • z) hB'
  exact ⟨v, by rw [hv]; exact hproj⟩


/-- The line matrix-centralizer calculation suffices for the intrinsic bound
in the full projective line parabolic. The matrix-shape premise remains explicit. -/
theorem line_centralizer_le_of_matrix_shape [Finite F] [CharP F 2]
    (hJ : J.form = 1) (hconj : ∀ x : F, J.conj x = x ^ 4)
    (hcard : Nat.card F = 16)
    (hshape : ∀ (c : F), c + J.conj c = 1 →
      ∀ A : Matrix (Fin 5) (Fin 5) F,
        (∀ v : LineCore.Coord J,
          A * LineCore.Parabolic.ambientMatrix J v =
            LineCore.Parabolic.ambientMatrix J v * A) →
        ∃ a b : F, A = lineCentralMatrix a b) :
    Subgroup.centralizer (LineCore.Parabolic.projectiveUnipotent J hJ : Set (lineParabolic J)) ≤
      LineCore.Parabolic.projectiveUnipotent J hJ := by
  obtain ⟨c, hc⟩ := exists_trace_one J hconj hcard
  intro g hg
  obtain ⟨A, hA, hAg⟩ := g.property
  have hm (v : LineCore.Coord J) :
      A.val.val * LineCore.Parabolic.ambientMatrix J v =
        LineCore.Parabolic.ambientMatrix J v * A.val.val := by
    have hp := Subgroup.mem_centralizer_iff.mp hg (LineCore.Parabolic.toParabolic J hJ v)
      (show LineCore.Parabolic.toParabolic J hJ v ∈
        LineCore.Parabolic.projectiveUnipotent J hJ from ⟨v, rfl⟩)
    have hp' := congrArg Subtype.val hp
    change project J (LineCore.Parabolic.toSU J hJ v) * g.val =
      g.val * project J (LineCore.Parabolic.toSU J hJ v) at hp'
    rw [← hAg] at hp'
    have hu : (LineCore.Parabolic.toSU J hJ v) ^ 4 = 1 := by
      rw [← map_pow, LineCore.Coord.fourth_power, map_one]
    have he := congrArg (fun B : J.specialSubgroup => B.val.val)
      (commute_of_project_commute_fourth_power J hconj hcard hp'.symm hu)
    change A.val.val * (LineCore.Parabolic.ambientGL J v).val =
      (LineCore.Parabolic.ambientGL J v).val * A.val.val at he
    rwa [LineCore.Parabolic.ambientGL_val] at he
  obtain ⟨a, b, hab⟩ := hshape c hc A.val.val hm
  obtain ⟨v, hv⟩ := line_image_of_shape J hJ hconj A a b hab
  exact ⟨v, Subtype.ext (hv.trans hAg)⟩

/-- The plane matrix-centralizer calculation suffices for the intrinsic bound
in the full projective plane parabolic. The matrix-shape premise remains explicit. -/
theorem plane_centralizer_le_of_matrix_shape [Finite F] [CharP F 2]
    (hJ : J.form = 1) (hconj : ∀ x : F, J.conj x = x ^ 4)
    (hcard : Nat.card F = 16)
    (hshape : ∀ (c : F), c + J.conj c = 1 →
      ∀ A : Matrix (Fin 5) (Fin 5) F,
        (∀ v : PlaneCore.Parameters J,
          A * PlaneCore.Parameters.ambientMatrix v =
            PlaneCore.Parameters.ambientMatrix v * A) →
        ∃ (a : F) (z : Matrix (Fin 2) (Fin 2) F), A = planeCentralMatrix a z) :
    Subgroup.centralizer (PlaneCore.projectiveUnipotent J hJ : Set (planeParabolic J)) ≤
      PlaneCore.projectiveUnipotent J hJ := by
  obtain ⟨c, hc⟩ := exists_trace_one J hconj hcard
  intro g hg
  obtain ⟨A, hA, hAg⟩ := g.property
  have hm (v : PlaneCore.Parameters J) :
      A.val.val * PlaneCore.Parameters.ambientMatrix v =
        PlaneCore.Parameters.ambientMatrix v * A.val.val := by
    have hp := Subgroup.mem_centralizer_iff.mp hg (PlaneCore.Parameters.toParabolic hJ v)
      (show PlaneCore.Parameters.toParabolic hJ v ∈
        PlaneCore.projectiveUnipotent J hJ from ⟨v, rfl⟩)
    have hp' := congrArg Subtype.val hp
    change project J (PlaneCore.Parameters.toSU hJ v) * g.val =
      g.val * project J (PlaneCore.Parameters.toSU hJ v) at hp'
    rw [← hAg] at hp'
    have hu : (PlaneCore.Parameters.toSU hJ v) ^ 4 = 1 := by
      rw [← map_pow, PlaneCore.Parameters.pow_four, map_one]
    have he := congrArg (fun B : J.specialSubgroup => B.val.val)
      (commute_of_project_commute_fourth_power J hconj hcard hp'.symm hu)
    change A.val.val * (PlaneCore.Parameters.ambientGL v).val =
      (PlaneCore.Parameters.ambientGL v).val * A.val.val at he
    rwa [PlaneCore.Parameters.ambientGL_val] at he
  obtain ⟨a, z, haz⟩ := hshape c hc A.val.val hm
  obtain ⟨v, hv⟩ := plane_image_of_shape J hJ hconj A a z haz
  exact ⟨v, Subtype.ext (hv.trans hAg)⟩

end Theory.SpecificGroups.UnitaryFive.RadicalCentralizers
