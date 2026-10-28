module
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorOrthogonal
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.LineTransport

/-!
# Singular-vector transport in the exterior-square split-six model

A Pfaffian-zero bivector with nonzero first coordinate is realized by an
explicit determinant-one chart. Six even coordinate permutations move any
nonzero coordinate to that chart. This gives exact vector transport over
any field. An upper unipotent matrix realizes each Siegel generator based
at the first singular vector, supplying the surjectivity step for D₃ = A₃.
The six integral permutation determinants are checked before scalar extension.

Source: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

open Matrix ClassicalOrthogonal
open Atlas.Order20160A8.Bivectors Atlas.Order20160A8.Exterior
open scoped MatrixGroups
namespace ClassicalOrthogonal.D3ExteriorComparison.GeneralTransport
variable {F : Type} [Field F]

noncomputable def chart (w : Six F) (hw : w 0 ≠ 0) : SL(4,F) :=
  ⟨!![1,0,0,0; 0,w 0,0,0; -(w 3)/(w 0),w 1,(w 0)⁻¹,0; -(w 4)/(w 0),w 2,0,1], by
    simp [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix_apply,Fin.succAbove,hw]⟩

private theorem chart_action (w : Six F) (hw : w 0 ≠ 0) (hq : pfaffian w = 0) :
    exteriorMap (chart w hw).val (Pi.single 0 1) = w := by
  ext i
  fin_cases i <;>
    simp [chart,exteriorMap,compound,first,second,Matrix.toLin'_apply,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · field_simp [hw]
  · field_simp [hw]
  · have hp := hq
    simp only [pfaffian_apply] at hp
    field_simp [hw]
    linear_combination -hp

private def pivotIntegral (i : Fin 6) : Matrix (Fin 4) (Fin 4) ℤ := ![
  1,
  !![1,0,0,0; 0,0,1,0; 0,0,0,1; 0,1,0,0],
  !![1,0,0,0; 0,0,0,1; 0,1,0,0; 0,0,1,0],
  !![0,1,0,0; 0,0,1,0; 1,0,0,0; 0,0,0,1],
  !![0,1,0,0; 0,0,0,1; 0,0,1,0; 1,0,0,0],
  !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]] i

private theorem pivotIntegral_det (i : Fin 6) : (pivotIntegral i).det = 1 := by
  revert i
  decide +kernel

private noncomputable def pivotMatrix (i : Fin 6) : Matrix (Fin 4) (Fin 4) F :=
  (pivotIntegral i).map (Int.castRingHom F)

private theorem pivotMatrix_det (i : Fin 6) : (pivotMatrix (F := F) i).det = 1 := by
  change ((Int.castRingHom F).mapMatrix (pivotIntegral i)).det = 1
  rw [← RingHom.map_det, pivotIntegral_det, map_one]


noncomputable def pivot (i : Fin 6) : SL(4,F) := ⟨pivotMatrix i,pivotMatrix_det i⟩

private theorem pivot_action_first (i : Fin 6) (w : Six F) :
    exteriorMap (pivot i).val w 0 = w i := by
  fin_cases i <;>
    simp [pivot,pivotMatrix,pivotIntegral,exteriorMap,compound,first,second,
      Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.one_apply]

public theorem bivector_transport (w : Six F) (hw : w ≠ 0) (hq : pfaffian w = 0) :
    ∃ g : SL(4,F), exteriorMap g.val (Pi.single 0 1) = w := by
  obtain ⟨i,hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hh
    exact hw (funext hh)
  let a := pivot (F := F) i
  let w' := exteriorMap a.val w
  have hw' : w' 0 ≠ 0 := by simpa only [w',a,pivot_action_first] using hi
  have hq' : pfaffian w' = 0 := by
    change pfaffian (exteriorMap a.val w) = 0
    rw [pfaffian_exteriorMap,a.det_coe,one_mul,hq]
  refine ⟨a⁻¹ * chart w' hw',?_⟩
  rw [SpecialLinearGroup.coe_mul,exteriorMap_mul,LinearMap.comp_apply,chart_action w' hw' hq']
  change exteriorMap a⁻¹.val (exteriorMap a.val w) = w
  rw [← LinearMap.comp_apply,← exteriorMap_mul,← SpecialLinearGroup.coe_mul,
    inv_mul_cancel,SpecialLinearGroup.coe_one,exteriorMap_one,LinearMap.id_apply]

public theorem singular_transport (v : VectorD 3 F) (hv : v ≠ 0) (hq : formD 3 F v = 0) :
    ∃ g : SL(4,F), (toOrthogonal g).val (e 0) = v := by
  let w := coordinates.symm v
  have hw : w ≠ 0 := by
    intro he
    apply hv
    have hh := congrArg coordinates he
    simpa only [w,LinearEquiv.apply_symm_apply,map_zero] using hh
  have hp : pfaffian w = 0 := by
    rw [← coordinates_form,show coordinates w = v from coordinates.apply_symm_apply v,hq]
  obtain ⟨g,hg⟩ := bivector_transport w hw hp
  refine ⟨g,?_⟩
  change coordinates (exteriorMap g.val (coordinates.symm (e 0))) = v
  have he : coordinates.symm (e (F := F) 0) = Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [coordinates,e]
  rw [he,hg]
  exact coordinates.apply_symm_apply v
@[expose] public noncomputable def upper (v : VectorD 3 F) : SL(4,F) :=
  ⟨!![1,0,-v (.inl 2),v (.inl 1);
       0,1,v (.inr 1),v (.inr 2);
       0,0,1,0;
       0,0,0,1], by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Matrix.submatrix_apply, Fin.succAbove]⟩

public theorem upper_action (v : VectorD 3 F) (hv : (formD 3 F).polarBilin (e 0) v = 0) :
    toOrthogonal (upper v) = siegelElement (formD 3 F) (e 0) v (formD_e 0) hv := by
  have hv0 : v (.inr 0) = 0 := by
    rw [Quadratic.polar_swap, polarD_e] at hv
    exact hv
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change coordinates (exteriorMap (upper v).val (coordinates.symm x)) = Quadratic.siegel (formD 3 F) (e 0) v x
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [-QuadraticMap.polarBilin_apply_apply, upper, coordinates, exteriorMap, compound, first, second, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Quadratic.siegel,
      formD_apply, polarD_apply, e, hv0] <;> ring

end ClassicalOrthogonal.D3ExteriorComparison.GeneralTransport
