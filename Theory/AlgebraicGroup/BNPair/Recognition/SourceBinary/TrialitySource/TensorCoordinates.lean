module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.TensorAction
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.RootParameters
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Coordinates and fixed axes of the cubic tensor

The tensor basis gives eight explicit coordinates for the three natural
factors through one field embedding and its two Frobenius twists. Upper
unipotent matrices determine the fixed line: Dedekind independence of the
three distinct field embeddings kills the other seven coordinates. This
argument includes the cubic field over F₂ without a special computation.
The same basis gives Weyl interchange, the complete upper action on the
opposite axis, and the cubic norm character on the highest axis.

TensorRootAxes applies these calculations to literal source roots in the
radical abelianization. No root-basis agreement or source commutator is
assumed by these matrix calculations.

Source: Fong--Seitz II (4.7)(b), printed pp.218--219, and the threefold
Frobenius tensor construction in TensorAction.
-/

@[expose] public noncomputable section
open scoped MatrixGroups TensorProduct MonoidAlgebra
open Representation Representation.SL2 Representation.SL2.BinarySmall
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorCoordinates
variable {F C : Type*} [Field F] [Field C]

abbrev Index := (Fin 2 × Fin 2) × Fin 2

def basis : Module.Basis Index C (TripleSpace C) :=
  ((Pi.basisFun C (Fin 2)).tensorProduct (Pi.basisFun C (Fin 2))).tensorProduct
    (Pi.basisFun C (Fin 2))

def coordinates : TripleSpace C ≃ₗ[C] (Index → C) := basis.equivFun

theorem coordinates_tmul (u v w : Fin 2 → C) (i j k : Fin 2) :
    coordinates ((u ⊗ₜ[C] v) ⊗ₜ[C] w) ((i,j),k) = u i*v j*w k := by
  simp [coordinates,basis,Module.Basis.equivFun_apply,mul_comm,mul_left_comm]

def matrix (κ : F →+* C) (σ : F ≃+* F) (g : SL(2,F)) : Matrix Index Index C :=
  fun r s => κ (g.val r.1.1 s.1.1)*κ (σ (g.val r.1.2 s.1.2))*
    κ (σ (σ (g.val r.2 s.2)))

theorem action (κ : F →+* C) (σ : F ≃+* F) (g : SL(2,F)) (v : TripleSpace C) :
    coordinates (TensorAction.cubicTensor κ σ g v) =
      (matrix κ σ g).mulVec (coordinates v) := by
  let R := TensorAction.cubicTensor κ σ
  suffices h : coordinates.toLinearMap.comp (R g) =
      (Matrix.toLin' (matrix κ σ g)).comp coordinates.toLinearMap from LinearMap.congr_fun h v
  apply TensorProduct.ext'
  intro x w
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [TensorProduct.add_tmul,map_add] using congrArg₂ (·+·) hx hy
  | tmul u v =>
    ext ⟨⟨i,j⟩,k⟩
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,Matrix.toLin'_apply,
      R,TensorAction.cubicTensor_tmul,coordinates_tmul]
    simp only [embeddedNatural,specialLinearNatural_apply,MonoidHom.comp_apply,
      Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
      matrix,Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,
      Matrix.map_apply,RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe,Finset.sum_mul,Finset.mul_sum,coordinates_tmul]
    simp only [Fin.sum_univ_two]
    ring

def upper (κ : F →+* C) (σ : F ≃+* F) (a : F) (v : Index → C) : Index → C :=
  (matrix κ σ (uni a)).mulVec v

theorem upper_000 (κ : F →+* C) (σ : F ≃+* F) (a : F) (v : Index → C) :
    upper κ σ a v ((0,0),0) =
      v ((0,0),0)+κ (σ (σ a))*v ((0,0),1)+κ (σ a)*v ((0,1),0)+
      κ (σ a)*κ (σ (σ a))*v ((0,1),1)+κ a*v ((1,0),0)+
      κ a*κ (σ (σ a))*v ((1,0),1)+κ a*κ (σ a)*v ((1,1),0)+
      κ a*κ (σ a)*κ (σ (σ a))*v ((1,1),1) := by
  simp [upper,matrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Fin.sum_univ_two,uni]
  ring

theorem upper_100 (κ : F →+* C) (σ : F ≃+* F) (a : F) (v : Index → C) :
    upper κ σ a v ((1,0),0) = v ((1,0),0)+κ (σ (σ a))*v ((1,0),1)+
      κ (σ a)*v ((1,1),0)+κ (σ a)*κ (σ (σ a))*v ((1,1),1) := by
  simp [upper,matrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_two,uni]
  ring

theorem upper_010 (κ : F →+* C) (σ : F ≃+* F) (a : F) (v : Index → C) :
    upper κ σ a v ((0,1),0) = v ((0,1),0)+κ (σ (σ a))*v ((0,1),1)+
      κ a*v ((1,1),0)+κ a*κ (σ (σ a))*v ((1,1),1) := by
  simp [upper,matrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_two,uni]
  ring

theorem upper_110 (κ : F →+* C) (σ : F ≃+* F) (a : F) (v : Index → C) :
    upper κ σ a v ((1,1),0) = v ((1,1),0)+κ (σ (σ a))*v ((1,1),1) := by
  simp [upper,matrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_two,uni]

theorem separate (κ : F →+* C) (σ : F ≃+* F)
    (hcube : ∀ a, σ (σ (σ a)) = a) (hne : ∃ a, σ a ≠ a)
    (x y z : C) (h : ∀ a, x*κ a+y*κ (σ a)+z*κ (σ (σ a)) = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  let f : Fin 3 → F →* C :=
    ![κ.toMonoidHom,(κ.comp σ.toRingHom).toMonoidHom,
      ((κ.comp σ.toRingHom).comp σ.toRingHom).toMonoidHom]
  have h01 : f 0 ≠ f 1 := by
    intro he
    obtain ⟨a,ha⟩ := hne
    exact ha (κ.injective (DFunLike.congr_fun he a)).symm
  have h02 : f 0 ≠ f 2 := by
    intro he
    obtain ⟨a,ha⟩ := hne
    have he' : a = σ (σ a) := κ.injective (DFunLike.congr_fun he a)
    exact ha ((congrArg σ he').trans (hcube a))
  have h12 : f 1 ≠ f 2 := by
    intro he
    obtain ⟨a,ha⟩ := hne
    have he' : σ a = σ (σ a) := κ.injective (DFunLike.congr_fun he a)
    exact ha (σ.injective he').symm
  have hi : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all
  have hli := (linearIndependent_monoidHom F C).comp f hi
  have hz := Fintype.linearIndependent_iff.mp hli ![x,y,z] (by
    ext a
    simpa [Fin.sum_univ_three,f] using h a)
  exact ⟨hz 0,hz 1,hz 2⟩

theorem fixed_support (κ : F →+* C) (σ : F ≃+* F)
    (hcube : ∀ a, σ (σ (σ a)) = a) (hne : ∃ a, σ a ≠ a)
    (v : Index → C) (h : ∀ a, upper κ σ a v = v) :
    ∀ r, r ≠ ((0,0),0) → v r = 0 := by
  have h111 : v ((1,1),1) = 0 := by
    have he := congrFun (h 1) ((1,1),0)
    simpa only [upper_110,map_one,one_mul,add_eq_left] using he
  have hpair : v ((1,1),0) = 0 ∧ v ((1,0),1) = 0 := by
    have he (a : F) := congrFun (h a) ((1,0),0)
    simp only [upper_100,h111,mul_zero,add_zero,add_assoc,add_eq_left] at he
    have hh := separate κ σ hcube hne 0 (v ((1,1),0)) (v ((1,0),1)) (by
      intro a
      simpa only [zero_mul,zero_add,mul_comm,add_comm] using he a)
    exact hh.2
  have h011 : v ((0,1),1) = 0 := by
    have he := congrFun (h 1) ((0,1),0)
    simpa only [upper_010,h111,hpair.1,map_one,one_mul,add_zero,add_eq_left] using he
  have hsingle : v ((1,0),0) = 0 ∧ v ((0,1),0) = 0 ∧ v ((0,0),1) = 0 := by
    apply separate κ σ hcube hne
    intro a
    have he := congrFun (h a) ((0,0),0)
    simp only [upper_000,h111,hpair.1,hpair.2,h011,mul_zero,add_zero,
      add_assoc,add_eq_left] at he
    simpa only [mul_comm,add_comm,add_left_comm,add_assoc] using he
  rintro ⟨⟨i,j⟩,k⟩ hr
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

theorem upper_fixed_iff (κ : F →+* C) (σ : F ≃+* F)
    (hcube : ∀ a, σ (σ (σ a)) = a) (hne : ∃ a, σ a ≠ a)
    (v : TripleSpace C) :
    (∀ a, TensorAction.cubicTensor κ σ (uni a) v = v) ↔
      ∃ c : C, v = c • basis ((0,0),0) := by
  constructor
  · intro h
    have hh : ∀ a, upper κ σ a (coordinates v) = coordinates v := by
      intro a
      rw [upper,← action,h a]
    refine ⟨coordinates v ((0,0),0),coordinates.injective ?_⟩
    ext r
    by_cases hr : r = ((0,0),0)
    · subst r
      simp [coordinates]
    · rw [fixed_support κ σ hcube hne _ hh r hr]
      simp [coordinates,hr]
  · rintro ⟨c,rfl⟩ a
    rw [map_smul]
    congr 1
    apply coordinates.injective
    rw [action]
    ext ⟨⟨i,j⟩,k⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [matrix,Matrix.mulVec,dotProduct,coordinates,uni]

variable [CharP F 2]

theorem weyl_coordinates (κ : F →+* C) (σ : F ≃+* F) (v : TripleSpace C)
    (i j k : Fin 2) :
    coordinates (TensorAction.cubicTensor κ σ (weyl F) v) ((i,j),k) =
      coordinates v ((1-i,1-j),1-k) := by
  rw [action]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [matrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_two,weyl]

theorem weyl_top (κ : F →+* C) (σ : F ≃+* F) :
    TensorAction.cubicTensor κ σ (weyl F) (basis ((0,0),0)) = basis ((1,1),1) := by
  apply coordinates.injective
  ext ⟨⟨i,j⟩,k⟩
  rw [weyl_coordinates]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [coordinates]

omit [CharP F 2] in
theorem upper_bottom (κ : F →+* C) (σ : F ≃+* F) (a : F) (c : C)
    (i j k : Fin 2) :
    coordinates (TensorAction.cubicTensor κ σ (uni a) (c • basis ((1,1),1))) ((i,j),k) =
      c*(if i = 0 then κ a else 1)*(if j = 0 then κ (σ a) else 1)*
        (if k = 0 then κ (σ (σ a)) else 1) := by
  rw [action]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [matrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fin.sum_univ_two,
      coordinates,uni,mul_comm,mul_left_comm]

omit [CharP F 2] in
theorem tor_top (κ : F →+* C) (σ : F ≃+* F) (t : Fˣ) :
    TensorAction.cubicTensor κ σ (tor t) (basis ((0,0),0)) =
      κ (t.val*σ t.val*σ (σ t.val)) • basis ((0,0),0) := by
  apply coordinates.injective
  rw [action]
  ext ⟨⟨i,j⟩,k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [matrix,Matrix.mulVec,dotProduct,coordinates,tor,map_mul]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource.TensorCoordinates




