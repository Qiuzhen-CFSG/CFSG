module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FivePaths.Apartment
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourRadicalCentralizers.Reduction

/-!
# The native PSU₅(4) rotation centralizer

Projective commutation with the native quarter-turn lifts to SU₅ because
the scalar kernel has order five and the rotation has fourth power one.
Fixation of the marked isotropic line and rotation equivariance restrict
the matrix to three parameters in the hyperbolic basis. The Hermitian
equations eliminate the off-diagonal parameter; determinant one makes the
remaining matrix scalar. Its image in PSU₅ is therefore trivial.

This proves the native defect calculation for Aschbacher–Smith F.4.10,16–17,
printed pp.279,282–283 of `refs/quasithin.pdf`, with matrix field sixteen
and unitary parameter four. No injectivity of SU₅ → PSU₅ is used.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveCartan
open PlaneCore FivePaths
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)

include hc hJ in
theorem coordinates_preserves (g : J.specialSubgroup) :
    J.conjTranspose (coordinates J c g).val * planeGram * (coordinates J c g).val =
      planeGram := by
  have hgram : J.conjTranspose (planeBasis c) * J.form * planeBasis c = planeGram :=
    planeBasis_gram J c hc hJ
  have hi : J.conjTranspose (planeBasisInv c) * J.conjTranspose (planeBasis c) = 1 := by
    rw [←ct_mul,planeBasis_mul_inv]
    change ((J.conj : F →+* F).mapMatrix 1).transpose = 1
    rw [map_one,Matrix.transpose_one]
  have hu := (J.mem_specialSubgroup_iff g.val).mp g.property |>.1
  rw [coordinates_val,ct_mul,ct_mul,←hgram]
  calc
    _ = J.conjTranspose (planeBasis c) * J.conjTranspose g.val.val *
        (J.conjTranspose (planeBasisInv c) * J.conjTranspose (planeBasis c)) *
        J.form * (planeBasis c * planeBasisInv c) * g.val.val * planeBasis c := by
          simp only [mul_assoc]
    _ = J.conjTranspose (planeBasis c) *
        (J.conjTranspose g.val.val * J.form * g.val.val) * planeBasis c := by
          rw [hi,planeBasis_mul_inv]
          simp only [mul_one,mul_assoc]
    _ = _ := by rw [hu]

theorem coordinates_det (g : J.specialSubgroup) : (coordinates J c g).val.det = 1 := by
  have hdU : GeneralLinearGroup.det g.val = 1 :=
    ((J.mem_specialSubgroup_iff g.val).mp g.property).2
  have hd : g.val.val.det = 1 := by
    simpa only [GeneralLinearGroup.val_det_apply,Units.val_one] using
      congrArg (fun u : Fˣ => (u : F)) hdU
  rw [coordinates_val,Matrix.det_mul,Matrix.det_mul,hd,mul_one,
    ←Matrix.det_mul,planeBasis_inv_mul,Matrix.det_one]

private theorem line_rotation_shape (g : J.specialSubgroup)
    (hl : g ∈ specialStabilizer J (line F))
    (hr : Commute g (rotation J c hc hJ)) :
    ∃ a b z : F, (coordinates J c g).val =
      !![a,0,z,0,0; 0,a,z,0,0; 0,0,b,0,0; 0,0,z,a,0; 0,0,z,0,a] := by
  let A := (coordinates J c g).val
  have he := congrArg (fun g : J.specialSubgroup => (coordinates J c g).val) hr.eq
  simp only [map_mul] at he
  change A * (coordinates J c (rotation J c hc hJ)).val =
    (coordinates J c (rotation J c hc hJ)).val * A at he
  rw [rotation_coordinates] at he
  have hcol (i : Fin 5) (hi : i ≠ 0) : A i 0 = 0 := coordinates_line J c g hl i hi
  have h10 := hcol 1 (by decide)
  have h20 := hcol 2 (by decide)
  have h30 := hcol 3 (by decide)
  have h40 := hcol 4 (by decide)
  refine ⟨A 0 0,A 2 2,A 0 2,?_⟩
  have hh := fun (i j : Fin 5) =>
    congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A i j) he
  simp only [Fin.forall_fin_succ,
    Matrix.mul_apply,Fin.sum_univ_succ] at hh
  simp at hh
  rcases hh with ⟨⟨h01,h03,h02,_,h00⟩,⟨h11,h13,h12,_,h10'⟩,
    ⟨h21,h23,h24,_⟩,⟨h31,h33,h32,h34,h30'⟩,⟨h41,h43,_,_,_⟩⟩
  ext i j
  change A i j = _
  fin_cases i <;> fin_cases j
  · rfl
  · exact h01.trans h40
  · rfl
  · exact h03.trans (h41.trans h30)
  · exact h10'.symm.trans h10
  · exact h10
  · exact h11
  · exact h12
  · exact h13.trans (h01.trans h40)
  · exact h30'.symm.trans h30
  · exact h20
  · exact h21.trans h20
  · rfl
  · exact h23.trans (h21.trans h20)
  · exact h24.trans (h23.trans (h21.trans h20))
  · exact h30
  · exact h31.trans h10
  · exact h32.trans h12
  · exact h33.trans h11
  · exact h34.trans (h13.trans (h01.trans h40))
  · exact h40
  · exact h41.trans h30
  · exact h02.symm
  · exact h43.trans (h31.trans h10)
  · exact h00.symm

/-- A projective point-stabilizer element commuting with the native quarter-turn
is trivial. Projective commutation lifts using the actual scalar kernel of order five. -/
theorem line_project_commute_rotation [Finite F]
    (hσ : ∀ x, J.conj x = x^4) (hcard : Nat.card F = 16)
    (g : J.specialSubgroup) (hl : g ∈ specialStabilizer J (line F))
    (hr : Commute (project J g) (project J (rotation J c hc hJ))) : project J g = 1 := by
  have hr' : Commute g (rotation J c hc hJ) :=
    RadicalCentralizers.commute_of_project_commute_fourth_power J hσ hcard hr.eq
      (rotation_fourth J c hc hJ)
  obtain ⟨a,b,z,he⟩ := line_rotation_shape J c hc hJ g hl hr'
  have hgram := coordinates_preserves J c hc hJ g
  rw [he] at hgram
  have hu := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A 0 3) hgram
  have hz := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A 0 2) hgram
  simp [HermitianForm.conjTranspose,planeGram,Matrix.mul_apply,Fin.sum_univ_succ] at hu hz
  have ha : a ≠ 0 := by intro ha; simp [ha] at hu
  have hz0 : z = 0 := hz.resolve_left ha
  have hdet := coordinates_det J c g
  have hdiag : (coordinates J c g).val = diagonal ![a,a,b,a,a] := by
    rw [he,hz0]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hdiag,Matrix.det_diagonal] at hdet
  simp only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.prod_univ_zero,mul_one] at hdet
  have ha5 : a^5 = 1 := by simpa only [hσ,←pow_succ] using hu
  have hb : b = a := by
    apply mul_left_cancel₀ (pow_ne_zero 4 ha)
    calc
      a^4*b = 1 := by linear_combination hdet
      _ = a^4*a := by simpa only [pow_succ] using ha5.symm
  let u : Fˣ := Units.mk0 a ha
  have hcoord : coordinates J c g = GeneralLinearGroup.scalar (Fin 5) u := by
    apply Units.ext
    rw [hdiag,hb,GeneralLinearGroup.coe_scalar]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar,u]
  have hg : g.val = GeneralLinearGroup.scalar (Fin 5) u := by
    have he' : (planeBasisGL c)⁻¹ * g.val * planeBasisGL c =
        GeneralLinearGroup.scalar (Fin 5) u := hcoord
    have hs : (planeBasisGL c)⁻¹ * GeneralLinearGroup.scalar (Fin 5) u * planeBasisGL c =
        GeneralLinearGroup.scalar (Fin 5) u := by
      have hcen : GeneralLinearGroup.scalar (Fin 5) u ∈ center (GL (Fin 5) F) := by
        rw [GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨u,rfl⟩
      rw [mem_center_iff.mp hcen (planeBasisGL c)⁻¹]
      group
    exact (MulAut.conj (planeBasisGL c)⁻¹).injective (he'.trans hs.symm)
  apply Subtype.ext
  change ProjGenLinGroup.mk g.val = 1
  rw [hg]
  exact ProjGenLinGroup.mk_scalar u
/-- The preceding calculation on the actual projective point stabilizer. -/
theorem projective_line_commute_rotation [Finite F]
    (hσ : ∀ x, J.conj x = x^4) (hcard : Nat.card F = 16)
    (g : ProjectiveSpecialUnitaryMatrixGroup J) (hg : g ∈ lineParabolic J)
    (hr : Commute g (project J (rotation J c hc hJ))) : g = 1 := by
  obtain ⟨a,ha,rfl⟩ := hg
  exact line_project_commute_rotation J c hc hJ hσ hcard a ha hr

end Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveCartan
