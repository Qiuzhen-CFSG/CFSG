module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveRoots
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Kernel

/-!
# Root, Cartan and Weyl generation of the unitary-five plane parabolic

The complete plane radical is an explicit product of the Hermitian root,
its pair-reflection conjugate, and a middle-reflection conjugate of the
linear root. Upper and lower linear roots generate the SL₂ Levi; its full
GL₂ extension is recovered by diagonal matrices. The existing literal
Levi factorization then gives every element of the plane parabolic.

These are identities in the actual special-unitary cover, including its
scalar kernel. They feed the projective automorphism rigidity consumer.
Source: Aschbacher–Smith F.1.12(7) and F.4.10,16–17,
pp.263–264,279,282–283 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveRootGeneration
open PlaneCore FivePaths FiveRoots
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)

private theorem pair_hermitian_coordinates (x z : F) (hz : z+J.conj z=x*J.conj x) :
    (coordinates J c (pairSwap J c hc hJ*hermitianRoot J hJ x z hz*(pairSwap J c hc hJ)⁻¹)).val =
      !![1,0,x,z,0;0,1,0,0,0;0,0,1,J.conj x,0;0,0,0,1,0;0,0,0,0,1] := by
  have hi : (pairSwap J c hc hJ)⁻¹=pairSwap J c hc hJ :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using pairSwap_sq J c hc hJ)
  rw [hi,map_mul,map_mul]
  change (coordinates J c (pairSwap J c hc hJ)).val*
    (coordinates J c (hermitianRoot J hJ x z hz)).val*(coordinates J c (pairSwap J c hc hJ)).val=_
  rw [coordinates_pairSwap,pair_matrix,hermitianRoot_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_succ]

private theorem middle_linear_coordinates (x : F) :
    (coordinates J c (middleSwap J c hc hJ*linearRoot J c hc hJ x*(middleSwap J c hc hJ)⁻¹)).val =
      !![1,0,0,0,x;0,1,0,J.conj x,0;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1] := by
  have hi : (middleSwap J c hc hJ)⁻¹=middleSwap J c hc hJ :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using middleSwap_sq J c hc hJ)
  rw [hi,map_mul,map_mul]
  change (coordinates J c (middleSwap J c hc hJ)).val*
    (coordinates J c (linearRoot J c hc hJ x)).val*(coordinates J c (middleSwap J c hc hJ)).val=_
  rw [coordinates_middleSwap,middle_matrix,linearRoot_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_succ]

omit [CharP F 2] in
private theorem pair_matrix_product (x y z w : F) :
    (!![1,0,x,z,0;0,1,0,0,0;0,0,1,J.conj x,0;0,0,0,1,0;0,0,0,0,1] : Matrix (Fin 5) (Fin 5) F)*
    !![1,0,0,0,0;0,1,y,0,w;0,0,1,0,J.conj y;0,0,0,1,0;0,0,0,0,1] =
    !![1,0,x,z,x*J.conj y;0,1,y,0,w;0,0,1,J.conj x,J.conj y;0,0,0,1,0;0,0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_succ]

private theorem radical_matrix_word (u : Parameters J) : u.matrix =
    !![1,0,u.x 0,u.z 0 0,0;0,1,0,0,0;0,0,1,J.conj (u.x 0),0;0,0,0,1,0;0,0,0,0,1]*
    !![1,0,0,0,0;0,1,u.x 1,0,u.z 1 1;0,0,1,0,J.conj (u.x 1);0,0,0,1,0;0,0,0,0,1]*
    !![1,0,0,0,J.conj (u.z 1 0);0,1,0,u.z 1 0,0;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1] := by
  rw [pair_matrix_product]
  have h01 : u.z 0 1=u.x 0*J.conj (u.x 1)+J.conj (u.z 1 0) := by
    have h := congrArg (fun z : F => z+J.conj (u.z 1 0)) (u.relation 0 1)
    simpa [add_assoc,CharTwo.add_self_eq_zero] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Parameters.matrix,Matrix.mul_apply,Fin.sum_univ_succ,h01,add_comm]

private theorem radical_word (u : Parameters J) :
    Parameters.toSU hJ u =
      (pairSwap J c hc hJ*hermitianRoot J hJ (u.x 0) (u.z 0 0) (u.relation 0 0)*
        (pairSwap J c hc hJ)⁻¹) *
      hermitianRoot J hJ (u.x 1) (u.z 1 1) (u.relation 1 1) *
      (middleSwap J c hc hJ*linearRoot J c hc hJ (J.conj (u.z 1 0))*
        (middleSwap J c hc hJ)⁻¹) := by
  apply coordinates_injective J c
  apply Units.ext
  rw [map_mul,map_mul]
  change (coordinates J c (Parameters.toSU hJ u)).val =
    (coordinates J c (pairSwap J c hc hJ*
      hermitianRoot J hJ (u.x 0) (u.z 0 0) (u.relation 0 0)*(pairSwap J c hc hJ)⁻¹)).val*
      (coordinates J c (hermitianRoot J hJ (u.x 1) (u.z 1 1) (u.relation 1 1))).val*
      (coordinates J c (middleSwap J c hc hJ*linearRoot J c hc hJ (J.conj (u.z 1 0))*
        (middleSwap J c hc hJ)⁻¹)).val
  rw [coordinates_parameters,pair_hermitian_coordinates,middle_linear_coordinates,hermitianRoot_coordinates]
  rw [J.conj_involutive]
  exact radical_matrix_word J u

/-- Both roots and the two native reflections contain the full plane radical. -/
theorem radical_le (H : Subgroup J.specialSubgroup)
    (hl : ∀ x, linearRoot J c hc hJ x∈H)
    (hh : ∀ x z hz, hermitianRoot J hJ x z hz∈H)
    (hs : middleSwap J c hc hJ∈H) (ht : pairSwap J c hc hJ∈H)
    (u : Parameters J) : Parameters.toSU hJ u∈H := by
  rw [radical_word J c hc hJ u]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem ht (hh _ _ _)) (H.inv_mem ht))
    (hh _ _ _)) (H.mul_mem (H.mul_mem hs (hl _)) (H.inv_mem hs))

private def swapSL : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0,1;1,0],by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩

private theorem swapSL_inv : (swapSL (F:=F))⁻¹=swapSL := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) F)*!![0,1;1,0]=1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_succ]

private theorem swap_levi : planeLeviSL J c hc hJ (swapSL (F:=F))=pairSwap J c hc hJ := by
  apply coordinates_injective J c
  apply Units.ext
  change (coordinates J c (planeLeviSU J c hc hJ (planeSLtoGL (swapSL (F:=F))))).val = _
  rw [coordinates_levi,coordinates_pairSwap,pair_matrix]
  have hi : (planeSLtoGL (swapSL (F:=F)))⁻¹=planeSLtoGL (swapSL (F:=F)) := by
    rw [←map_inv]
    congr 1
    exact swapSL_inv
  change planeBlockMatrix J (planeSLtoGL (swapSL (F:=F))) = _
  simp only [planeBlockMatrix,planeMiddleScalar,planeSLtoGL_det,map_one,inv_one,mul_one]
  rw [show (planeSLtoGL (swapSL (F:=F))).inv=(planeSLtoGL (swapSL (F:=F))).val from congrArg Units.val hi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeSLtoGL,swapSL,planeAdjoint]

private theorem lower_word (x : F) :
    planeLeviSL J c hc hJ (SpecialLinearGroup.transvection (i:=(1:Fin 2)) (j:=0) one_ne_zero x) =
      pairSwap J c hc hJ*linearRoot J c hc hJ x*(pairSwap J c hc hJ)⁻¹ := by
  rw [←swap_levi]
  change planeLeviSL J c hc hJ _ = planeLeviSL J c hc hJ (swapSL (F:=F))*
    planeLeviSL J c hc hJ (SpecialLinearGroup.upperUnipotentHom F (Multiplicative.ofAdd x))*
      (planeLeviSL J c hc hJ (swapSL (F:=F)))⁻¹
  rw [←map_inv,←map_mul,←map_mul]
  congr 1
  rw [swapSL_inv]
  apply Subtype.ext
  change (SpecialLinearGroup.transvection (i:=(1:Fin 2)) (j:=0) one_ne_zero x).val =
    (swapSL (F:=F)).val*(SpecialLinearGroup.upperUnipotentHom F (Multiplicative.ofAdd x)).val*(swapSL (F:=F)).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapSL,SpecialLinearGroup.transvection_coe,SpecialLinearGroup.upperUnipotentHom,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem specialLevi_le (H : Subgroup J.specialSubgroup)
    (hl : ∀ x, linearRoot J c hc hJ x∈H) (ht : pairSwap J c hc hJ∈H)
    (A : SpecialLinearGroup (Fin 2) F) : planeLeviSL J c hc hJ A∈H := by
  apply Matrix.SL2.transvection_induction (fun A => planeLeviSL J c hc hJ A∈H)
  · intro i j hij x
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hl x
    · rw [lower_word]
      exact H.mul_mem (H.mul_mem ht (hl x)) (H.inv_mem ht)
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [map_mul]
    exact H.mul_mem hA hB

def diagonalGL (a b : Fˣ) : GL (Fin 2) F where
  val := Matrix.diagonal ![(a:F),(b:F)]
  inv := Matrix.diagonal ![(a:F)⁻¹,(b:F)⁻¹]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

private theorem diagonalLevi (a b : Fˣ) :
    FiveDiagonal.IsDiagonal J c (planeLeviSU J c hc hJ (diagonalGL a b)) := by
  refine ⟨![(a:F),(b:F),planeMiddleScalar J (diagonalGL a b),(J.conj (a:F))⁻¹,(J.conj (b:F))⁻¹],?_⟩
  rw [coordinates_levi]
  change planeBlockMatrix J (diagonalGL a b) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeBlockMatrix,planeAdjoint,diagonalGL]

theorem levi_le (H : Subgroup J.specialSubgroup)
    (hl : ∀ x, linearRoot J c hc hJ x∈H) (ht : pairSwap J c hc hJ∈H)
    (hD : ∀ g, FiveDiagonal.IsDiagonal J c g → g∈H) (A : GL (Fin 2) F) :
    planeLeviSU J c hc hJ A∈H := by
  let d : Fˣ := GeneralLinearGroup.det A
  let D := diagonalGL d 1
  have hd : GeneralLinearGroup.det D=d := by
    apply Units.ext
    change (Matrix.diagonal ![(d:F),1]).det=(d:F)
    simp
  have hdet : GeneralLinearGroup.det (D⁻¹*A)=1 := by
    rw [map_mul,map_inv,hd]
    exact inv_mul_cancel d
  let S : SpecialLinearGroup (Fin 2) F := ⟨(D⁻¹*A).val,congrArg Units.val hdet⟩
  have hS : planeSLtoGL S=D⁻¹*A := Units.ext rfl
  have he : A=D*planeSLtoGL S := by rw [hS]; group
  rw [he,map_mul]
  exact H.mul_mem (hD _ (diagonalLevi J c hc hJ d 1))
    (specialLevi_le J c hc hJ H hl ht S)

/-- The literal root, Cartan and Weyl elements generate the entire native
plane parabolic, including all projective scalars in its SU preimage. -/
theorem plane_le (H : Subgroup J.specialSubgroup)
    (hl : ∀ x, linearRoot J c hc hJ x∈H)
    (hh : ∀ x z hz, hermitianRoot J hJ x z hz∈H)
    (hs : middleSwap J c hc hJ∈H) (ht : pairSwap J c hc hJ∈H)
    (hD : ∀ g, FiveDiagonal.IsDiagonal J c g → g∈H) : specialStabilizer J (plane F)≤H := by
  intro g hg
  obtain ⟨u,hu⟩ := planeStabilizer_factorization J c hc hJ ⟨g,hg⟩
  have he := congrArg Subtype.val hu
  change g=Parameters.toSU hJ u*planeLeviSU J c hc hJ _ at he
  rw [he]
  exact H.mul_mem (radical_le J c hc hJ H hl hh hs ht u) (levi_le J c hc hJ H hl ht hD _)

end Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveRootGeneration
