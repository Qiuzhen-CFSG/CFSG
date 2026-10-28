module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveRoots
public import Theory.SpecificGroups.SU3.EvenSemilinear.Rigidity

/-!
# Pointwise rigidity of the actual unitary-five simple roots

The full diagonal Cartan scales the linear root over the field, forcing an
involutory root-preserving automorphism to act trivially. The actual
Hermitian root embeds faithfully in PSU₅ through the existing plane
unipotent parametrization. Its coordinate automorphism has scalar first
coordinate, again forced to one by its square. The existing norm-one
Heisenberg rigidity theorem eliminates its remaining central shear.

All weights are calculated in the native coordinates (0,3),(1,4), with
index two fixed. The SU₅ projective scalar kernel is retained; only the
specific root embeddings are proved injective.

Source: the direct Cartan route in Aschbacher–Smith F.4.10,16–17,
pp.279,282–283; the reused Heisenberg calculation is Steinberg Theorem 36,
steps (2), (4), (7), `refs/KGroup/GLS3/Chapter2St1.tex`.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveRootCoordinates
open PlaneCore FivePaths FiveRoots
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)

/-- The ternary form supplies only the existing Heisenberg coordinate group. -/
def ternaryForm : HermitianForm 3 F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := !![0,0,1;0,1,0;1,0,0]
  form_hermitian := by intro i j; fin_cases i <;> fin_cases j <;> simp
  form_nondegenerate := by simp [Matrix.det_fin_three]

abbrev Coord := hermitianUnipotentCoord (ternaryForm J)

theorem relation (z : Coord J) : z.val.2+J.conj z.val.2=z.val.1*J.conj z.val.1 :=
  (eq_neg_of_add_eq_zero_left z.property).trans (CharTwo.neg_eq _)

def parameterHom : Coord J →* Parameters J where
  toFun z := hermitianParameter J z.val.1 z.val.2 (relation J z)
  map_one' := by
    apply Parameters.ext
    · ext i; fin_cases i <;> rfl
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' z w := by
    apply Parameters.ext
    · ext i; fin_cases i <;> simp [hermitianParameter,Parameters.mul_x]
      rfl
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hermitianParameter,Parameters.mul_z]
      change z.val.2+w.val.2-z.val.1*J.conj w.val.1 = _
      rw [CharTwo.sub_eq_add]

def rootHom : Coord J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (planeParabolic J).subtype.comp ((Parameters.toParabolic hJ).comp (parameterHom J))

@[simp] theorem rootHom_apply (z : Coord J) :
    rootHom J hJ z=project J (hermitianRoot J hJ z.val.1 z.val.2 (relation J z)) := rfl

theorem rootHom_injective : Function.Injective (rootHom J hJ) := by
  apply (planeParabolic J).subtype_injective.comp
  apply (Parameters.toParabolic_injective hJ).comp
  intro z w h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun p : Parameters J => p.x 1) h)
    (congrArg (fun p : Parameters J => p.z 1 1) h)

def diagonalGL (u : Fˣ) : GL (Fin 2) F where
  val := Matrix.diagonal ![(u:F)⁻¹,(u:F)]
  inv := Matrix.diagonal ![(u:F),(u:F)⁻¹]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

def torus (u : Fˣ) : J.specialSubgroup := planeLeviSU J c hc hJ (diagonalGL u)

theorem torus_coordinates (u : Fˣ) : (coordinates J c (torus J c hc hJ u)).val =
    Matrix.diagonal ![(u:F)⁻¹,(u:F),1,J.conj (u:F),(J.conj (u:F))⁻¹] := by
  rw [torus,coordinates_levi]
  change planeBlockMatrix J (diagonalGL u) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeBlockMatrix,planeMiddleScalar,planeAdjoint,diagonalGL]

theorem torus_diagonal (u : Fˣ) : FiveDiagonal.IsDiagonal J c (torus J c hc hJ u) :=
  ⟨_,torus_coordinates J c hc hJ u⟩

def scale (u : Fˣ) (z : Coord J) : Coord J :=
  ⟨((u:F)*z.val.1,((u:F)*J.conj (u:F))*z.val.2),by
    change ((u:F)*J.conj (u:F))*z.val.2 +
      J.conj (((u:F)*J.conj (u:F))*z.val.2) +
        ((u:F)*z.val.1)*J.conj ((u:F)*z.val.1) = 0
    have hz : z.val.2+J.conj z.val.2+z.val.1*J.conj z.val.1=0 := z.property
    simp only [map_mul]
    rw [J.conj_involutive]
    linear_combination ((u:F)*J.conj (u:F))*hz⟩

omit [CharP F 2] in
@[simp] theorem scale_first (u : Fˣ) (z : Coord J) :
    (scale J u z).val.1 = (u:F)*z.val.1 := rfl
omit [CharP F 2] in
@[simp] theorem scale_second (u : Fˣ) (z : Coord J) :
    (scale J u z).val.2 = ((u:F)*J.conj (u:F))*z.val.2 := rfl

theorem torus_root (u : Fˣ) (z : Coord J) :
    project J (torus J c hc hJ u)*rootHom J hJ z*(project J (torus J c hc hJ u))⁻¹ =
      rootHom J hJ (scale J u z) := by
  rw [rootHom_apply,rootHom_apply,←map_inv,←map_mul,←map_mul]
  congr 1
  apply mul_inv_eq_iff_eq_mul.mpr
  apply coordinates_injective J c
  apply Units.ext
  rw [map_mul,map_mul]
  change (coordinates J c (torus J c hc hJ u)).val*
    (coordinates J c (hermitianRoot J hJ z.val.1 z.val.2 (relation J z))).val =
    (coordinates J c (hermitianRoot J hJ _ _ _)).val * (coordinates J c (torus J c hc hJ u)).val
  rw [torus_coordinates,hermitianRoot_coordinates,hermitianRoot_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul,Matrix.mul_diagonal,scale,map_mul,mul_assoc,mul_comm,mul_left_comm, (map_ne_zero J.conj).mpr u.ne_zero]
  field_simp



/-- Restriction of an actual involutory projective automorphism to the native root. -/
def coordinateAut (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a^2=1)
    (hR : ∀ z : Coord J, ∃ w : Coord J, a (rootHom J hJ z)=rootHom J hJ w) : MulAut (Coord J) := by
  let f : Coord J → Coord J := fun z => Classical.choose (hR z)
  have hf (z : Coord J) : rootHom J hJ (f z)=a (rootHom J hJ z) := (Classical.choose_spec (hR z)).symm
  have hi (z : Coord J) : f (f z)=z := by
    apply rootHom_injective J hJ
    rw [hf,hf]
    exact DFunLike.congr_fun ha (rootHom J hJ z)
  exact
    { toFun := f
      invFun := f
      left_inv := hi
      right_inv := hi
      map_mul' := by
        intro z w
        apply rootHom_injective J hJ
        rw [hf,map_mul,map_mul,map_mul,hf,hf] }

theorem coordinateAut_spec (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a^2=1)
    (hR : ∀ z : Coord J, ∃ w : Coord J, a (rootHom J hJ z)=rootHom J hJ w) (z : Coord J) :
    rootHom J hJ (coordinateAut J hJ a ha hR z)=a (rootHom J hJ z) :=
  (Classical.choose_spec (hR z)).symm

theorem coordinateAut_square (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a^2=1)
    (hR : ∀ z : Coord J, ∃ w : Coord J, a (rootHom J hJ z)=rootHom J hJ w) :
    coordinateAut J hJ a ha hR ^ 2=1 := by
  apply DFunLike.ext
  intro z
  apply rootHom_injective J hJ
  change rootHom J hJ (coordinateAut J hJ a ha hR (coordinateAut J hJ a ha hR z))=rootHom J hJ z
  rw [coordinateAut_spec,coordinateAut_spec]
  exact DFunLike.congr_fun ha (rootHom J hJ z)

include hc in
theorem coordinateAut_scale (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a^2=1)
    (hR : ∀ z : Coord J, ∃ w : Coord J, a (rootHom J hJ z)=rootHom J hJ w)
    (hD : ∀ g, FiveDiagonal.IsDiagonal J c g → a (project J g)=project J g)
    (u : Fˣ) (z : Coord J) :
    coordinateAut J hJ a ha hR (scale J u z)=scale J u (coordinateAut J hJ a ha hR z) := by
  apply rootHom_injective J hJ
  rw [coordinateAut_spec,←torus_root J c hc hJ,←torus_root J c hc hJ,
    map_mul,map_mul,map_inv,hD _ (torus_diagonal J c hc hJ u),coordinateAut_spec]

include hc in
private theorem first_fixed (φ : MulAut (Coord J)) (hφ : φ^2=1)
    (hscale : ∀ u z, φ (scale J u z)=scale J u (φ z)) : ∀ z, (φ z).val.1=z.val.1 := by
  let z₁ : Coord J := ⟨(1,c),by change c+J.conj c+1*J.conj 1=0; simp [hc,CharTwo.add_self_eq_zero]⟩
  let y : F := (φ z₁).val.1
  have hscalar (z : Coord J) : (φ z).val.1=z.val.1*y := by
    by_cases hz : z.val.1=0
    · rw [HermitianForm.EvenSemilinear.coordAut_first_zero (ternaryForm J) φ z hz,hz,zero_mul]
    let u : Fˣ := Units.mk0 z.val.1 hz
    have he : z.val.1=(scale J u z₁).val.1 := by simp [scale_first,u,z₁]
    have h := HermitianForm.EvenSemilinear.coordAut_first_eq (ternaryForm J) φ z (scale J u z₁) he
    rw [hscale] at h
    exact h
  have hy : y^2=1 := by
    have hh := congrArg (fun z : Coord J => z.val.1) (DFunLike.congr_fun hφ z₁)
    change (φ (φ z₁)).val.1=1 at hh
    rw [hscalar] at hh
    simpa only [pow_two] using hh
  have hy1 : y=1 := CharTwo.sq_injective (hy.trans (one_pow 2).symm)
  intro z
  simpa only [hy1,mul_one] using hscalar z

omit [CharP F 2] in
private theorem torusAction_eq_scale (k : Fˣ) (z : Coord J) :
    hermitianTorusAction (ternaryForm J) k z =
      scale J (k*(Units.map J.conj.toMonoidHom k)⁻¹^2) z := by
  apply Subtype.ext
  apply Prod.ext
  · rw [hermitianTorusAction_fst (ternaryForm J) k z,scale_first]
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,Units.coe_map]
    change z.val.1*(k:F)*(J.conj (k:F))⁻¹^2 =
      ((k:F)*(J.conj (k:F))⁻¹^2)*z.val.1
    ring
  · rw [hermitianTorusAction_snd (ternaryForm J) k z,scale_second]
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,Units.coe_map]
    change z.val.2*(J.conj (k:F))⁻¹*(k:F)⁻¹ =
      ((k:F)*(J.conj (k:F))⁻¹^2)*J.conj ((k:F)*(J.conj (k:F))⁻¹^2)*z.val.2
    rw [map_mul,map_pow,map_inv₀,J.conj_involutive]
    field_simp

include hc in
/-- The literal Heisenberg root is fixed pointwise: the involution kills its
first scalar, and the existing norm-one calculation eliminates the central shear. -/
theorem fixes_hermitianRoot [Finite F]
    (hcard : Nat.card F=16) (hfixed : Nat.card {x : F // J.conj x=x}=4)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a^2=1)
    (hD : ∀ g, FiveDiagonal.IsDiagonal J c g → a (project J g)=project J g)
    (hR : ∀ x z hz, ∃ y v hv,
      a (project J (hermitianRoot J hJ x z hz))=project J (hermitianRoot J hJ y v hv)) :
    ∀ x z hz, a (project J (hermitianRoot J hJ x z hz))=project J (hermitianRoot J hJ x z hz) := by
  have hR' (z : Coord J) : ∃ w : Coord J, a (rootHom J hJ z)=rootHom J hJ w := by
    obtain ⟨y,v,hv,he⟩ := hR z.val.1 z.val.2 (relation J z)
    refine ⟨⟨(y,v),?_⟩,he⟩
    change v+J.conj v+y*J.conj y=0
    rw [hv,CharTwo.add_self_eq_zero]
  let φ := coordinateAut J hJ a ha hR'
  have hscale := coordinateAut_scale J c hc hJ a ha hR' hD
  have hfirst := first_fixed J c hc φ (coordinateAut_square J hJ a ha hR') hscale
  obtain ⟨k,_,hk3,_,hk⟩ :=
    exists_hermitian_norm_one_torus_cube_ne_one (ternaryForm J) 4 hcard hfixed rfl (by decide)
  have hφ : φ=1 := HermitianForm.EvenSemilinear.coordAut_eq_one_of_first_fixed
    (ternaryForm J) hcard hfixed φ hfirst k hk hk3 (by
      intro z
      rw [torusAction_eq_scale,torusAction_eq_scale,hscale])
  intro x z hz
  let w : Coord J := ⟨(x,z),by change z+J.conj z+x*J.conj x=0; rw [hz,CharTwo.add_self_eq_zero]⟩
  have he := coordinateAut_spec J hJ a ha hR' w
  change rootHom J hJ (φ w)=a (rootHom J hJ w) at he
  rw [hφ] at he
  exact he.symm



private theorem linear_injective : Function.Injective (fun x : F => project J (linearRoot J c hc hJ x)) := by
  intro x y he
  have h : planeSLParabolic J c hc hJ (SpecialLinearGroup.upperUnipotentHom F (Multiplicative.ofAdd x))=
      planeSLParabolic J c hc hJ (SpecialLinearGroup.upperUnipotentHom F (Multiplicative.ofAdd y)) := Subtype.ext he
  have hh := (planeSLParabolic_injective J c hc hJ) h
  simpa [SpecialLinearGroup.upperUnipotentHom,SpecialLinearGroup.transvection_coe] using
    congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val 0 1) hh

private theorem linear_zero : linearRoot J c hc hJ 0=1 := by
  change planeLeviSL J c hc hJ (SpecialLinearGroup.upperUnipotentHom F 1)=1
  rw [map_one,map_one]

private theorem torus_linear (u : Fˣ) (x : F) :
    torus J c hc hJ u⁻¹*linearRoot J c hc hJ x*(torus J c hc hJ u⁻¹)⁻¹ =
      linearRoot J c hc hJ ((u:F)^2*x) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply coordinates_injective J c
  apply Units.ext
  rw [map_mul,map_mul]
  change (coordinates J c (torus J c hc hJ u⁻¹)).val *
    (coordinates J c (linearRoot J c hc hJ x)).val =
    (coordinates J c (linearRoot J c hc hJ ((u:F)^2*x))).val *
      (coordinates J c (torus J c hc hJ u⁻¹)).val
  rw [torus_coordinates,linearRoot_coordinates,linearRoot_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul,Matrix.mul_diagonal,pow_two,map_mul,
      mul_assoc,mul_comm,(map_ne_zero J.conj).mpr u.ne_zero]

/-- The full Cartan and involution relation force pointwise linear-root fixation. -/
theorem fixes_linearRoot [Finite F]
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a^2=1)
    (hD : ∀ g, FiveDiagonal.IsDiagonal J c g → a (project J g)=project J g)
    (hR : ∀ x, ∃ y, a (project J (linearRoot J c hc hJ x))=project J (linearRoot J c hc hJ y)) :
    ∀ x, a (project J (linearRoot J c hc hJ x))=project J (linearRoot J c hc hJ x) := by
  let r : F → ProjectiveSpecialUnitaryMatrixGroup J := fun x => project J (linearRoot J c hc hJ x)
  obtain ⟨y,hy⟩ := hR 1
  have scalar (x : F) : a (r x)=r (x*y) := by
    by_cases hx : x=0
    · simp [r,hx,linear_zero]
    obtain ⟨v,hv⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R:=F))) x
    have hv0 : v≠0 := by intro h; simp [h] at hv; exact hx hv.symm
    let u : Fˣ := Units.mk0 v hv0
    let d := project J (torus J c hc hJ u⁻¹)
    have hd : a d=d := hD _ (torus_diagonal J c hc hJ u⁻¹)
    have ht (z : F) : d*r z*d⁻¹=r ((u:F)^2*z) := by
      simpa only [map_mul,map_inv] using congrArg (project J) (torus_linear J c hc hJ u z)
    have h1 : d*r 1*d⁻¹=r x := by simpa only [u,Units.val_mk0,hv,mul_one] using ht 1
    rw [←h1,map_mul,map_mul,map_inv,hd,hy,ht]
    simp only [u,Units.val_mk0,hv]
  have hy2 : y^2=1 := by
    apply linear_injective J c hc hJ
    have hh := DFunLike.congr_fun ha (r 1)
    change a (a (r 1))=r 1 at hh
    rw [hy,scalar] at hh
    simpa only [pow_two] using hh
  have hy1 : y=1 := CharTwo.sq_injective (hy2.trans (one_pow 2).symm)
  intro x
  simpa only [hy1,mul_one] using scalar x

end Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveRootCoordinates
