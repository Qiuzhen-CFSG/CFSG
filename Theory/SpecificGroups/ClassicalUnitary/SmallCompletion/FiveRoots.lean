module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveDiagonal
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourScalarKernel
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# The actual simple-root intersections in Hermitian five-space

The native flag stabilizer and its conjugate by each length-three Weyl
word intersect in a diagonal group times one simple root. Elements with
fourth power one have trivial diagonal part in characteristic two. This
recovers the additive linear root and the nonabelian Hermitian root in
the actual coordinates pairing (0,3) and (1,4).

For PSU₅(4), a representative is replaced by its fifth power. The genuine
order-five scalar kernel then gives a representative of fourth power one,
without assuming injectivity of SU₅ → PSU₅. Thus preservation of the two
parabolics and fixation of the marked reflections preserve both roots.
Pointwise fixation is a separate step.

Source: the Cartan apartment route in Aschbacher–Smith F.4.10,16–17,
printed pp.279,282–283 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveRoots
open PlaneCore FivePaths
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)

def linearRoot (x : F) : J.specialSubgroup :=
  planeLeviSL J c hc hJ (SpecialLinearGroup.upperUnipotentHom F (Multiplicative.ofAdd x))

def hermitianParameter (x z : F) (hz : z + J.conj z = x * J.conj x) : Parameters J :=
  ⟨![0,x],!![0,0;0,z],by intro i j; fin_cases i <;> fin_cases j <;> simp [hz]⟩

def hermitianRoot (x z : F) (hz : z + J.conj z = x * J.conj x) : J.specialSubgroup :=
  Parameters.toSU hJ (hermitianParameter J x z hz)

theorem coordinates_levi (A : GL (Fin 2) F) :
    coordinates J c (planeLeviSU J c hc hJ A) = planeBlockGL J A := by
  change (planeBasisGL c)⁻¹ * (planeBasisGL c * planeBlockGL J A * (planeBasisGL c)⁻¹) *
    planeBasisGL c = _
  group

theorem linearRoot_coordinates (x : F) : (coordinates J c (linearRoot J c hc hJ x)).val =
    !![1,x,0,0,0;0,1,0,0,0;0,0,1,0,0;0,0,0,1,0;0,0,0,J.conj x,1] := by
  change (coordinates J c (planeLeviSU J c hc hJ (planeSLtoGL _))).val = _
  rw [coordinates_levi]
  have hi : (planeSLtoGL (SpecialLinearGroup.upperUnipotentHom F (Multiplicative.ofAdd x)))⁻¹ =
      planeSLtoGL (SpecialLinearGroup.upperUnipotentHom F (Multiplicative.ofAdd x)) := by
    rw [←map_inv,←map_inv]
    congr 2
    change -x=x
    exact CharTwo.neg_eq x
  change planeBlockMatrix J _ = _
  simp only [planeBlockMatrix,planeMiddleScalar,planeSLtoGL_det,map_one,inv_one,mul_one]
  rw [show (planeSLtoGL (SpecialLinearGroup.upperUnipotentHom F (Multiplicative.ofAdd x))).inv =
    (planeSLtoGL (SpecialLinearGroup.upperUnipotentHom F (Multiplicative.ofAdd x))).val from congrArg Units.val hi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeAdjoint,planeSLtoGL,SpecialLinearGroup.upperUnipotentHom,
      SpecialLinearGroup.transvection_coe]

theorem hermitianRoot_coordinates (x z : F) (hz : z + J.conj z = x * J.conj x) :
    (coordinates J c (hermitianRoot J hJ x z hz)).val =
      !![1,0,0,0,0;0,1,x,0,z;0,0,1,0,J.conj x;0,0,0,1,0;0,0,0,0,1] := by
  rw [hermitianRoot,coordinates_parameters]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianParameter,Parameters.matrix]

def linearOpp : J.specialSubgroup := rotation J c hc hJ ^ 2 * pairSwap J c hc hJ
def hermitianOpp : J.specialSubgroup := rotation J c hc hJ ^ 2 * middleSwap J c hc hJ

theorem linearOpp_coordinates : (coordinates J c (linearOpp J c hc hJ)).val =
    !![0,0,0,0,1;0,0,0,1,0;0,0,1,0,0;0,1,0,0,0;1,0,0,0,0] := by
  rw [linearOpp,map_mul]
  change (coordinates J c (rotation J c hc hJ ^ 2)).val *
    (coordinates J c (pairSwap J c hc hJ)).val = _
  rw [rotation_sq_coordinates,coordinates_pairSwap,pair_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeGram,Matrix.mul_apply,Fin.sum_univ_succ]

theorem hermitianOpp_coordinates : (coordinates J c (hermitianOpp J c hc hJ)).val =
    !![0,0,0,1,0;0,1,0,0,0;0,0,1,0,0;1,0,0,0,0;0,0,0,0,1] := by
  rw [hermitianOpp,map_mul]
  change (coordinates J c (rotation J c hc hJ ^ 2)).val *
    (coordinates J c (middleSwap J c hc hJ)).val = _
  rw [rotation_sq_coordinates,coordinates_middleSwap,middle_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeGram,Matrix.mul_apply,Fin.sum_univ_succ]

theorem linearOpp_inv : (linearOpp J c hc hJ)⁻¹ = linearOpp J c hc hJ := by
  apply inv_eq_of_mul_eq_one_left
  apply coordinates_injective J c
  apply Units.ext
  rw [map_mul,map_one]
  change (coordinates J c (linearOpp J c hc hJ)).val *
    (coordinates J c (linearOpp J c hc hJ)).val = 1
  rw [linearOpp_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_succ]

theorem hermitianOpp_inv : (hermitianOpp J c hc hJ)⁻¹ = hermitianOpp J c hc hJ := by
  apply inv_eq_of_mul_eq_one_left
  apply coordinates_injective J c
  apply Units.ext
  rw [map_mul,map_one]
  change (coordinates J c (hermitianOpp J c hc hJ)).val *
    (coordinates J c (hermitianOpp J c hc hJ)).val = 1
  rw [hermitianOpp_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_succ]

private theorem linear_shape (g : J.specialSubgroup)
    (hg : g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F))
    (hw : linearOpp J c hc hJ*g*(linearOpp J c hc hJ)⁻¹∈
      specialStabilizer J (line F) ⊓ specialStabilizer J (plane F)) :
    let A := (coordinates J c g).val
    A=!![A 0 0,A 0 1,0,0,0;0,A 1 1,0,0,0;0,0,A 2 2,0,0;0,0,0,A 3 3,0;0,0,0,A 4 3,A 4 4] := by
  let A := (coordinates J c g).val
  have h10 : A 1 0=0 := coordinates_line J c g hg.1 1 (by decide)
  have h20 : A 2 0=0 := coordinates_line J c g hg.1 2 (by decide)
  have h30 : A 3 0=0 := coordinates_line J c g hg.1 3 (by decide)
  have h40 : A 4 0=0 := coordinates_line J c g hg.1 4 (by decide)
  have h21 : A 2 1=0 := coordinates_plane J c g hg.2 2 1 (by simp) (by simp)
  have h31 : A 3 1=0 := coordinates_plane J c g hg.2 3 1 (by simp) (by simp)
  have h41 : A 4 1=0 := coordinates_plane J c g hg.2 4 1 (by simp) (by simp)
  have he : (coordinates J c (linearOpp J c hc hJ*g*(linearOpp J c hc hJ)⁻¹)).val =
      (coordinates J c (linearOpp J c hc hJ)).val*A*(coordinates J c (linearOpp J c hc hJ)).val := by
    rw [linearOpp_inv,map_mul,map_mul]
    rfl
  have hz04 := coordinates_line J c _ hw.1 4 (by decide)
  rw [he,linearOpp_coordinates] at hz04
  have h04 : A 0 4=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz04
  have hz14 := coordinates_line J c _ hw.1 3 (by decide)
  rw [he,linearOpp_coordinates] at hz14
  have h14 : A 1 4=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz14
  have hz24 := coordinates_line J c _ hw.1 2 (by decide)
  rw [he,linearOpp_coordinates] at hz24
  have h24 : A 2 4=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz24
  have hz34 := coordinates_line J c _ hw.1 1 (by decide)
  rw [he,linearOpp_coordinates] at hz34
  have h34 : A 3 4=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz34
  have hz03 := coordinates_plane J c _ hw.2 4 1 (by simp) (by simp)
  rw [he,linearOpp_coordinates] at hz03
  have h03 : A 0 3=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz03
  have hz13 := coordinates_plane J c _ hw.2 3 1 (by simp) (by simp)
  rw [he,linearOpp_coordinates] at hz13
  have h13 : A 1 3=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz13
  have hz23 := coordinates_plane J c _ hw.2 2 1 (by simp) (by simp)
  rw [he,linearOpp_coordinates] at hz23
  have h23 : A 2 3=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz23
  have hu := FiveCartan.coordinates_preserves J c hc hJ g
  change J.conjTranspose A*planeGram*A=planeGram at hu
  have u03 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 0 3) hu
  have u14 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 1 4) hu
  have u02 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 0 2) hu
  have u42 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 4 2) hu
  have u12 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 1 2) hu
  have u32 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 3 2) hu
  simp [HermitianForm.conjTranspose,planeGram,Matrix.mul_apply,Fin.sum_univ_succ,h10,h20,h30,h40,h21,h31,h41,h04,h14,h24,h34,h03,h13,h23] at u03 u14 u02 u42 u12 u32
  have h32 : A 3 2=0 := u02.resolve_left (by intro h; simp [h] at u03)
  have h12 : A 1 2=0 := u42.resolve_left (by intro h; simp [h] at u14)
  have h42 : A 4 2=0 := by
    rw [h32,mul_zero,zero_add] at u12
    exact (mul_eq_zero.mp u12).resolve_left (by intro h; simp [h] at u14)
  have h02 : A 0 2=0 := by
    rw [h12,mul_zero,add_zero] at u32
    exact (mul_eq_zero.mp u32).resolve_left (by
      intro h
      have h0 : A 3 3 = 0 := J.conj.injective (by simpa using h)
      simp [h0] at u03)
  change A=_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10,h20,h30,h40,h21,h31,h41,h04,h14,h24,h34,h03,h13,h23,h32,h12,h42,h02] <;> rfl

private theorem hermitian_shape (g : J.specialSubgroup)
    (hg : g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F))
    (hw : hermitianOpp J c hc hJ*g*(hermitianOpp J c hc hJ)⁻¹∈
      specialStabilizer J (line F) ⊓ specialStabilizer J (plane F)) :
    let A := (coordinates J c g).val
    A=!![A 0 0,0,0,0,0;0,A 1 1,A 1 2,0,A 1 4;0,0,A 2 2,0,A 2 4;0,0,0,A 3 3,0;0,0,0,0,A 4 4] := by
  let A := (coordinates J c g).val
  have h10 : A 1 0=0 := coordinates_line J c g hg.1 1 (by decide)
  have h20 : A 2 0=0 := coordinates_line J c g hg.1 2 (by decide)
  have h30 : A 3 0=0 := coordinates_line J c g hg.1 3 (by decide)
  have h40 : A 4 0=0 := coordinates_line J c g hg.1 4 (by decide)
  have h21 : A 2 1=0 := coordinates_plane J c g hg.2 2 1 (by simp) (by simp)
  have h31 : A 3 1=0 := coordinates_plane J c g hg.2 3 1 (by simp) (by simp)
  have h41 : A 4 1=0 := coordinates_plane J c g hg.2 4 1 (by simp) (by simp)
  have he : (coordinates J c (hermitianOpp J c hc hJ*g*(hermitianOpp J c hc hJ)⁻¹)).val =
      (coordinates J c (hermitianOpp J c hc hJ)).val*A*(coordinates J c (hermitianOpp J c hc hJ)).val := by
    rw [hermitianOpp_inv,map_mul,map_mul]
    rfl
  have hz03 := coordinates_line J c _ hw.1 3 (by decide)
  rw [he,hermitianOpp_coordinates] at hz03
  have h03 : A 0 3=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz03
  have hz13 := coordinates_line J c _ hw.1 1 (by decide)
  rw [he,hermitianOpp_coordinates] at hz13
  have h13 : A 1 3=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz13
  have hz23 := coordinates_line J c _ hw.1 2 (by decide)
  rw [he,hermitianOpp_coordinates] at hz23
  have h23 : A 2 3=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz23
  have hz43 := coordinates_line J c _ hw.1 4 (by decide)
  rw [he,hermitianOpp_coordinates] at hz43
  have h43 : A 4 3=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz43
  have hz01 := coordinates_plane J c _ hw.2 3 1 (by simp) (by simp)
  rw [he,hermitianOpp_coordinates] at hz01
  have h01 : A 0 1=0 := by simpa [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] using hz01
  have hu := FiveCartan.coordinates_preserves J c hc hJ g
  change J.conjTranspose A*planeGram*A=planeGram at hu
  have u03 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 0 3) hu
  have u14 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 1 4) hu
  have u02 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 0 2) hu
  have u04 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 0 4) hu
  have u32 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 3 2) hu
  have u34 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 3 4) hu
  have u12 := congrArg (fun D : Matrix (Fin 5) (Fin 5) F => D 1 2) hu
  simp [HermitianForm.conjTranspose,planeGram,Matrix.mul_apply,Fin.sum_univ_succ,h10,h20,h30,h40,h21,h31,h41,h03,h13,h23,h43,h01] at u03 u14 u02 u04 u32 u34 u12
  have h32 : A 3 2=0 := u02.resolve_left (by intro h; simp [h] at u03)
  have h34 : A 3 4=0 := u04.resolve_left (by intro h; simp [h] at u03)
  have h02 : A 0 2=0 := u32.resolve_left (by intro h; simp [h] at u03)
  have h04 : A 0 4=0 := u34.resolve_left (by intro h; simp [h] at u03)
  have h42 : A 4 2=0 := u12.resolve_left (by intro h; simp [h] at u14)
  change A=_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10,h20,h30,h40,h21,h31,h41,h03,h13,h23,h43,h01,h32,h34,h02,h04,h42] <;> rfl



private theorem fourth_diagonal_linear (g : J.specialSubgroup)
    (hs : let A := (coordinates J c g).val
      A=!![A 0 0,A 0 1,0,0,0;0,A 1 1,0,0,0;0,0,A 2 2,0,0;0,0,0,A 3 3,0;0,0,0,A 4 3,A 4 4])
    (hp : g^4=1) (i : Fin 5) : (coordinates J c g).val i i = 1 := by
  have hh := congrArg (fun v : J.specialSubgroup => (coordinates J c v).val) hp
  rw [map_pow,map_one] at hh
  change (coordinates J c g).val^4=1 at hh
  have hi := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A i i) hh
  rw [hs] at hi
  apply CharTwo.sq_injective
  apply CharTwo.sq_injective
  fin_cases i <;> simpa [pow_succ,Matrix.mul_apply,Fin.sum_univ_succ,mul_assoc] using hi

private theorem fourth_diagonal_hermitian (g : J.specialSubgroup)
    (hs : let A := (coordinates J c g).val
      A=!![A 0 0,0,0,0,0;0,A 1 1,A 1 2,0,A 1 4;0,0,A 2 2,0,A 2 4;0,0,0,A 3 3,0;0,0,0,0,A 4 4])
    (hp : g^4=1) (i : Fin 5) : (coordinates J c g).val i i = 1 := by
  have hh := congrArg (fun v : J.specialSubgroup => (coordinates J c v).val) hp
  rw [map_pow,map_one] at hh
  change (coordinates J c g).val^4=1 at hh
  have hi := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A i i) hh
  rw [hs] at hi
  apply CharTwo.sq_injective
  apply CharTwo.sq_injective
  fin_cases i <;> simpa [pow_succ,Matrix.mul_apply,Fin.sum_univ_succ,mul_assoc] using hi

theorem linear_intersection (g : J.specialSubgroup)
    (hg : g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F))
    (hw : linearOpp J c hc hJ*g*(linearOpp J c hc hJ)⁻¹∈
      specialStabilizer J (line F) ⊓ specialStabilizer J (plane F))
    (hp : g^4=1) : ∃ x, g=linearRoot J c hc hJ x := by
  have hs := linear_shape J c hc hJ g hg hw
  have hd := fourth_diagonal_linear J c g hs hp
  have hs' : (coordinates J c g).val =
      !![1,(coordinates J c g).val 0 1,0,0,0;0,1,0,0,0;0,0,1,0,0;
        0,0,0,1,0;0,0,0,(coordinates J c g).val 4 3,1] := by simpa [hd] using hs
  have hu := FiveCartan.coordinates_preserves J c hc hJ g
  rw [hs'] at hu
  have hx := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A 1 3) hu
  simp [HermitianForm.conjTranspose,planeGram,Matrix.mul_apply,Fin.sum_univ_succ] at hx
  have hx' : (coordinates J c g).val 4 3 = J.conj ((coordinates J c g).val 0 1) := by
    exact ((eq_neg_of_add_eq_zero_left hx).trans (CharTwo.neg_eq _)).symm
  refine ⟨(coordinates J c g).val 0 1,?_⟩
  apply coordinates_injective J c
  apply Units.ext
  rw [linearRoot_coordinates,hs',hx']
  rfl

theorem hermitian_intersection (g : J.specialSubgroup)
    (hg : g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F))
    (hw : hermitianOpp J c hc hJ*g*(hermitianOpp J c hc hJ)⁻¹∈
      specialStabilizer J (line F) ⊓ specialStabilizer J (plane F))
    (hp : g^4=1) : ∃ x z hz, g=hermitianRoot J hJ x z hz := by
  have hs := hermitian_shape J c hc hJ g hg hw
  have hd := fourth_diagonal_hermitian J c g hs hp
  have hs' : (coordinates J c g).val =
      !![1,0,0,0,0;0,1,(coordinates J c g).val 1 2,0,(coordinates J c g).val 1 4;
        0,0,1,0,(coordinates J c g).val 2 4;0,0,0,1,0;0,0,0,0,1] := by simpa [hd] using hs
  have hu := FiveCartan.coordinates_preserves J c hc hJ g
  rw [hs'] at hu
  have hx := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A 2 4) hu
  have hz := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A 4 4) hu
  simp [HermitianForm.conjTranspose,planeGram,Matrix.mul_apply,Fin.sum_univ_succ] at hx hz
  have hx' : (coordinates J c g).val 2 4 = J.conj ((coordinates J c g).val 1 2) := by
    exact (eq_neg_of_add_eq_zero_left hx).trans (CharTwo.neg_eq _)
  rw [hx'] at hz
  have hz' : (coordinates J c g).val 1 4 + J.conj ((coordinates J c g).val 1 4) =
      (coordinates J c g).val 1 2 * J.conj ((coordinates J c g).val 1 2) := by
    have h := congrArg (fun x : F => x + (coordinates J c g).val 1 2 *
      J.conj ((coordinates J c g).val 1 2)) hz
    simpa [add_assoc,add_comm,add_left_comm,CharTwo.add_self_eq_zero] using h
  refine ⟨_,_,hz',?_⟩
  apply coordinates_injective J c
  apply Units.ext
  rw [hermitianRoot_coordinates,hs',hx']
  rfl



theorem linearRoot_mem_flag [Finite F] (x : F) :
    linearRoot J c hc hJ x ∈ specialStabilizer J (line F) ⊓ specialStabilizer J (plane F) := by
  constructor
  · apply (FiveFixed.mem_line_iff J c _).mpr
    intro i hi
    rw [linearRoot_coordinates]
    fin_cases i <;> simp_all
  · apply (FiveFixed.mem_plane_iff J c _).mpr
    intro i j hi hj
    rw [linearRoot_coordinates]
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl <;> rfl

include c in
theorem hermitianRoot_mem_flag [Finite F] (x z : F) (hz : z+J.conj z=x*J.conj x) :
    hermitianRoot J hJ x z hz ∈ specialStabilizer J (line F) ⊓ specialStabilizer J (plane F) := by
  constructor
  · apply (FiveFixed.mem_line_iff J c _).mpr
    intro i hi
    rw [hermitianRoot_coordinates]
    fin_cases i <;> simp_all
  · apply (FiveFixed.mem_plane_iff J c _).mpr
    intro i j hi hj
    rw [hermitianRoot_coordinates]
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl <;> rfl

theorem linearRoot_sq (x : F) : linearRoot J c hc hJ x ^ 2 = 1 := by
  apply coordinates_injective J c
  apply Units.ext
  rw [map_pow,map_one]
  change (coordinates J c (linearRoot J c hc hJ x)).val^2=1
  rw [linearRoot_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two,Matrix.mul_apply,Fin.sum_univ_succ,CharTwo.add_self_eq_zero]

theorem hermitianRoot_fourth (x z : F) (hz : z+J.conj z=x*J.conj x) :
    hermitianRoot J hJ x z hz ^ 4 = 1 := by
  change Parameters.toSU hJ _ ^ 4 = 1
  rw [←map_pow,Parameters.pow_four,map_one]

theorem linearRoot_conj (x : F) :
    linearOpp J c hc hJ * linearRoot J c hc hJ x * (linearOpp J c hc hJ)⁻¹ =
      linearRoot J c hc hJ (J.conj x) := by
  apply coordinates_injective J c
  apply Units.ext
  rw [linearOpp_inv,map_mul,map_mul]
  change (coordinates J c (linearOpp J c hc hJ)).val *
    (coordinates J c (linearRoot J c hc hJ x)).val *
    (coordinates J c (linearOpp J c hc hJ)).val = _
  rw [linearOpp_coordinates,linearRoot_coordinates,linearRoot_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_succ]

theorem hermitianRoot_conj (x z : F) (hz : z+J.conj z=x*J.conj x) :
    hermitianOpp J c hc hJ * hermitianRoot J hJ x z hz * (hermitianOpp J c hc hJ)⁻¹ =
      hermitianRoot J hJ x z hz := by
  apply coordinates_injective J c
  apply Units.ext
  rw [hermitianOpp_inv,map_mul,map_mul]
  change (coordinates J c (hermitianOpp J c hc hJ)).val *
    (coordinates J c (hermitianRoot J hJ x z hz)).val *
    (coordinates J c (hermitianOpp J c hc hJ)).val = _
  rw [hermitianOpp_coordinates,hermitianRoot_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_succ]

omit [CharP F 2] in
private theorem projective_fourth_lift [Finite F]
    (hconj : ∀ x, J.conj x=x^4) (hcard : Nat.card F=16)
    (w : J.specialSubgroup) (b : ProjectiveSpecialUnitaryMatrixGroup J)
    (hb : b∈lineParabolic J ⊓ planeParabolic J)
    (hw : project J w*b*(project J w)⁻¹∈lineParabolic J ⊓ planeParabolic J)
    (hp : b^4=1) :
    ∃ g : J.specialSubgroup, project J g=b ∧
      g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F) ∧
      w*g*w⁻¹∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F) ∧ g^4=1 := by
  let H := specialStabilizer J (line F) ⊓ specialStabilizer J (plane F)
  have hk : (project J).ker ≤ H := le_inf
    (ker_project_le_specialStabilizer J _) (ker_project_le_specialStabilizer J _)
  have hm : H.map (project J)=lineParabolic J ⊓ planeParabolic J := parabolic_inf J _ _
  have hpre (g : J.specialSubgroup) : project J g∈lineParabolic J ⊓ planeParabolic J ↔ g∈H := by
    rw [←hm]
    change g∈(H.map (project J)).comap (project J) ↔ g∈H
    rw [Subgroup.comap_map_eq_self hk]
  obtain ⟨v,rfl⟩ := project_surjective J b
  have hv := (hpre v).mp hb
  have hvw : w*v*w⁻¹∈H := (hpre _).mp (by simpa only [map_mul,map_inv] using hw)
  have hv4 : v^4∈(project J).ker := by simpa only [MonoidHom.mem_ker,map_pow] using hp
  have hk5 := pow_card_eq_one' (x := (⟨v^4,hv4⟩ : (project J).ker))
  rw [card_project_kernel J hconj hcard] at hk5
  have hv20 : (v^5)^4=1 := by
    have h := congrArg Subtype.val hk5
    change (v^4)^5=1 at h
    simpa only [←pow_mul] using h
  refine ⟨v^5,?_,H.pow_mem hv 5,?_,hv20⟩
  · rw [map_pow,pow_succ,hp,one_mul]
  · simpa only [conj_pow] using H.pow_mem hvw 5

theorem projective_linear_intersection [Finite F]
    (hconj : ∀ x, J.conj x=x^4) (hcard : Nat.card F=16)
    (b : ProjectiveSpecialUnitaryMatrixGroup J)
    (hb : b∈lineParabolic J ⊓ planeParabolic J)
    (hw : project J (linearOpp J c hc hJ)*b*(project J (linearOpp J c hc hJ))⁻¹∈
      lineParabolic J ⊓ planeParabolic J) (hp : b^4=1) :
    ∃ x, b=project J (linearRoot J c hc hJ x) := by
  obtain ⟨g,hg,hB,hw,hp⟩ := projective_fourth_lift J hconj hcard _ b hb hw hp
  obtain ⟨x,rfl⟩ := linear_intersection J c hc hJ g hB hw hp
  exact ⟨x,hg.symm⟩

theorem projective_hermitian_intersection [Finite F]
    (hconj : ∀ x, J.conj x=x^4) (hcard : Nat.card F=16)
    (b : ProjectiveSpecialUnitaryMatrixGroup J)
    (hb : b∈lineParabolic J ⊓ planeParabolic J)
    (hw : project J (hermitianOpp J c hc hJ)*b*(project J (hermitianOpp J c hc hJ))⁻¹∈
      lineParabolic J ⊓ planeParabolic J) (hp : b^4=1) :
    ∃ x z hz, b=project J (hermitianRoot J hJ x z hz) := by
  obtain ⟨g,hg,hB,hw,hp⟩ := projective_fourth_lift J hconj hcard _ b hb hw hp
  obtain ⟨x,z,hz,rfl⟩ := hermitian_intersection J c hc hJ g hB hw hp
  exact ⟨x,z,hz,hg.symm⟩



theorem preserves_projective_linearRoot [Finite F]
    (hconj : ∀ x, J.conj x=x^4) (hcard : Nat.card F=16)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hB : ∀ b∈lineParabolic J ⊓ planeParabolic J, a b∈lineParabolic J ⊓ planeParabolic J)
    (hs : a (project J (middleSwap J c hc hJ))=project J (middleSwap J c hc hJ))
    (ht : a (project J (pairSwap J c hc hJ))=project J (pairSwap J c hc hJ))
    (x : F) : ∃ y, a (project J (linearRoot J c hc hJ x))=project J (linearRoot J c hc hJ y) := by
  have hop : a (project J (linearOpp J c hc hJ))=project J (linearOpp J c hc hJ) := by
    simp only [linearOpp,rotation,map_mul,map_pow,hs,ht]
  have hmem (x : F) : project J (linearRoot J c hc hJ x)∈lineParabolic J ⊓ planeParabolic J := by
    have h := linearRoot_mem_flag J c hc hJ x
    exact ⟨⟨_,h.1,rfl⟩,⟨_,h.2,rfl⟩⟩
  apply projective_linear_intersection J c hc hJ hconj hcard _ (hB _ (hmem x))
  · have hh := congrArg (fun g => a (project J g)) (linearRoot_conj J c hc hJ x)
    simp only [map_mul,map_inv,hop] at hh
    rw [hh]
    exact hB _ (hmem (J.conj x))
  · have hp : linearRoot J c hc hJ x ^ 4=1 := by
      calc
        _ = (linearRoot J c hc hJ x ^ 2)^2 := pow_mul (linearRoot J c hc hJ x) 2 2
        _ = 1 := by rw [linearRoot_sq,one_pow]
    simpa only [map_pow,map_one] using congrArg (fun g => a (project J g)) hp

theorem preserves_projective_hermitianRoot [Finite F]
    (hconj : ∀ x, J.conj x=x^4) (hcard : Nat.card F=16)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hB : ∀ b∈lineParabolic J ⊓ planeParabolic J, a b∈lineParabolic J ⊓ planeParabolic J)
    (hs : a (project J (middleSwap J c hc hJ))=project J (middleSwap J c hc hJ))
    (ht : a (project J (pairSwap J c hc hJ))=project J (pairSwap J c hc hJ))
    (x z : F) (hz : z+J.conj z=x*J.conj x) :
    ∃ y v hv, a (project J (hermitianRoot J hJ x z hz))=project J (hermitianRoot J hJ y v hv) := by
  have hop : a (project J (hermitianOpp J c hc hJ))=project J (hermitianOpp J c hc hJ) := by
    simp only [hermitianOpp,rotation,map_mul,map_pow,hs,ht]
  have hmem : project J (hermitianRoot J hJ x z hz)∈lineParabolic J ⊓ planeParabolic J := by
    have h := hermitianRoot_mem_flag J c hJ x z hz
    exact ⟨⟨_,h.1,rfl⟩,⟨_,h.2,rfl⟩⟩
  apply projective_hermitian_intersection J c hc hJ hconj hcard _ (hB _ hmem)
  · have hh := congrArg (fun g => a (project J g)) (hermitianRoot_conj J c hc hJ x z hz)
    simp only [map_mul,map_inv,hop] at hh
    rw [hh]
    exact hB _ hmem
  · simpa only [map_pow,map_one] using
      congrArg (fun g => a (project J g)) (hermitianRoot_fourth J hJ x z hz)

end Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveRoots
