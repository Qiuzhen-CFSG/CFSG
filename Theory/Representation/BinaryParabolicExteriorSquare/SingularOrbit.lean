module
public import Theory.Representation.BinaryParabolicExteriorSquare.SingularPresentation

/-!
# Point and line transitivity in the binary exterior six-space

A coordinate shuffle moves a nonzero bivector coefficient to 01. The
Pfaffian equation then supplies an explicit lower triangular matrix
sending wedge 01 to the vector. Inside its stabilizer, two independent
coordinate swaps and another triangular matrix similarly reach every
singular neighbour. Consequently every ordered singular line is the
image of wedges 01 and 02 under one actual SL₄(2) element.

These are the point-orbit and line-transitivity inputs for B.4.13, used
in Aschbacher--Smith, The Classification of Quasithin Groups, 13.8.29(5),
printed p.964. Only the determinants of the small coordinate permutations are
checked by finite reduction; the orbit and line arguments are structural.
The imported exterior construction retains its ATLAS attribution and license.
-/

@[expose] public noncomputable section
open Atlas.Order20160A8.Bivectors
open scoped MatrixGroups
namespace Representation.BinaryParabolicExteriorSquare.SingularPresentation
open Representation.BinaryParabolicExteriorSquare

private def shuffleMatrix : Fin 6 → Matrix (Fin 4) (Fin 4) Bit := ![
  1,
  !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1],
  !![1,0,0,0; 0,0,0,1; 0,0,1,0; 0,1,0,0],
  !![0,0,1,0; 0,1,0,0; 1,0,0,0; 0,0,0,1],
  !![0,0,0,1; 0,1,0,0; 0,0,1,0; 1,0,0,0],
  !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]]

private theorem shuffle_det (i : Fin 6) : (shuffleMatrix i).det = 1 := by
  fin_cases i <;> decide +kernel

private def shuffle (i : Fin 6) : SL(4,Bit) := ⟨shuffleMatrix i,shuffle_det i⟩

private theorem shuffle_coordinate (i : Fin 6) (x : Six) :
    exteriorMap (shuffle i).val x 0 = x i := by
  fin_cases i <;>
    simp [shuffle,shuffleMatrix,exteriorMap,compound,first,second,
      Matrix.toLin'_apply,Matrix.mulVec,Matrix.one_apply,dotProduct,Fin.sum_univ_succ,
      ZMod.neg_eq_self_mod_two]

private def chart (x : Six) : SL(4,Bit) :=
  ⟨!![1,0,0,0; 0,1,0,0; x 3,x 1,1,0; x 4,x 2,0,1],by
    simp [Matrix.det_succ_row_zero,Fin.sum_univ_succ]⟩

private theorem chart_point (x : Six) (h0 : x 0 = 1) (hx : pfaffian x = 0) :
    exteriorMap (chart x).val (Pi.single 0 1) = x := by
  have he : x 3 * x 2 - x 4 * x 1 = x 5 := by
    rw [pfaffian_apply,h0,one_mul] at hx
    calc
      x 3 * x 2 - x 4 * x 1 = -(x 5) := by linear_combination hx
      _ = x 5 := ZMod.neg_eq_self_mod_two _
  rw [←wedge_basis 0,exteriorMap_wedge]
  ext i
  fin_cases i <;>
    simp [chart,wedge,first,second,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h0,he]

/-- Every nonzero singular bivector belongs to the orbit of the original
coordinate wedge 01 under the actual special linear group. -/
theorem singular_orbit (x : Six) (hx : pfaffian x = 0) (hne : x ≠ 0) :
    ∃ g : SL(4,Bit), exteriorMap g.val (Pi.single 0 1) = x := by
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (funext hn)
  have hi1 : x i = 1 := ((by decide : ∀ c : Bit, c = 0 ∨ c = 1) (x i)).resolve_left hi
  let y := exteriorMap (shuffle i).val x
  have hy0 : y 0 = 1 := (shuffle_coordinate i x).trans hi1
  have hy : pfaffian y = 0 := by
    rw [pfaffian_exteriorMap,hx,mul_zero]
  refine ⟨(shuffle i)⁻¹ * chart y,?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul,exteriorMap_mul,LinearMap.comp_apply,chart_point y hy0 hy]
  exact (Atlas.Order20160A8.Exterior.exteriorAction (shuffle i)).left_inv x

private def planeShuffleMatrix : Fin 4 → Matrix (Fin 4) (Fin 4) Bit := ![
  1,
  !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0],
  !![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1],
  !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]]

private def planeShuffle (i : Fin 4) : SL(4,Bit) :=
  ⟨planeShuffleMatrix i,by fin_cases i <;> decide +kernel⟩

private theorem planeShuffle_point (i : Fin 4) :
    exteriorMap (planeShuffle i).val (Pi.single 0 1) = (Pi.single 0 1 : Six) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [planeShuffle,planeShuffleMatrix,exteriorMap,compound,first,second,
      Matrix.toLin'_apply,Matrix.one_apply]

private theorem planeShuffle_coordinate (i : Fin 4) (x : Six) :
    exteriorMap (planeShuffle i).val x 1 = x i.succ.castSucc := by
  fin_cases i <;>
    simp [planeShuffle,planeShuffleMatrix,exteriorMap,compound,first,second,
      Matrix.toLin'_apply,Matrix.mulVec,Matrix.one_apply,dotProduct,Fin.sum_univ_succ]

private def lineChart (x : Six) : SL(4,Bit) :=
  ⟨!![1,0,0,0; x 3,1,x 0,0; 0,0,1,0; 0,0,x 2,1],by
    simp [Matrix.det_succ_row_zero,Fin.sum_univ_succ]⟩

private theorem lineChart_point (x : Six) :
    exteriorMap (lineChart x).val (Pi.single 0 1) = (Pi.single 0 1 : Six) := by
  rw [←wedge_basis 0,exteriorMap_wedge]
  ext i
  fin_cases i <;>
    simp [lineChart,wedge,first,second,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

private theorem lineChart_second (x : Six) (h1 : x 1 = 1) (h5 : x 5 = 0)
    (hx : pfaffian x = 0) :
    exteriorMap (lineChart x).val (Pi.single 1 1) = x := by
  have h4 : x 3 * x 2 = x 4 := by
    rw [pfaffian_apply,h1,h5,mul_zero,one_mul] at hx
    linear_combination hx
  rw [←wedge_basis 1,exteriorMap_wedge]
  ext i
  fin_cases i <;>
    simp [lineChart,wedge,first,second,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h1,h5,h4]

private theorem adjacent_last (x : Six) (hx : pfaffian x = 0)
    (hs : pfaffian ((Pi.single 0 1 : Six) + x) = 0) : x 5 = 0 := by
  have hs' : (1+x 0)*x 5-x 1*x 4+x 2*x 3 = 0 := by
    simpa [pfaffian_apply] using hs
  rw [pfaffian_apply] at hx
  linear_combination hs' - hx

/-- The stabilizer of wedge 01 is transitive on its singular neighbours. -/
theorem singular_neighbour_orbit (x : Six) (hx : pfaffian x = 0)
    (hs : pfaffian ((Pi.single 0 1 : Six) + x) = 0)
    (hne : x ≠ 0) (hdiff : x ≠ Pi.single 0 1) :
    ∃ g : SL(4,Bit), exteriorMap g.val (Pi.single 0 1) = (Pi.single 0 1 : Six) ∧
      exteriorMap g.val (Pi.single 1 1) = x := by
  have h5 := adjacent_last x hx hs
  obtain ⟨i,hi⟩ : ∃ i : Fin 4, x i.succ.castSucc ≠ 0 := by
    by_contra hn
    push Not at hn
    have h0 : x 0 = 0 ∨ x 0 = 1 := by exact (by decide : ∀ c : Bit, c = 0 ∨ c = 1) _
    rcases h0 with h0 | h0
    · apply hne
      ext j
      fin_cases j
      · exact h0
      · exact hn 0
      · exact hn 1
      · exact hn 2
      · exact hn 3
      · exact h5
    · apply hdiff
      ext j
      fin_cases j
      · simpa using h0
      · simpa using hn 0
      · simpa using hn 1
      · simpa using hn 2
      · simpa using hn 3
      · simpa using h5
  have hi1 : x i.succ.castSucc = 1 :=
    ((by decide : ∀ c : Bit, c = 0 ∨ c = 1) _).resolve_left hi
  let y := exteriorMap (planeShuffle i).val x
  have hy1 : y 1 = 1 := (planeShuffle_coordinate i x).trans hi1
  have hy : pfaffian y = 0 := by rw [pfaffian_exteriorMap,hx,mul_zero]
  have hys : pfaffian ((Pi.single 0 1 : Six) + y) = 0 := by
    rw [←planeShuffle_point i,←map_add,pfaffian_exteriorMap,hs,mul_zero]
  refine ⟨(planeShuffle i)⁻¹ * lineChart y,?_,?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul,exteriorMap_mul,LinearMap.comp_apply,lineChart_point]
    calc
      exteriorMap (planeShuffle i)⁻¹.val (Pi.single 0 1) =
          exteriorMap (planeShuffle i)⁻¹.val
            (exteriorMap (planeShuffle i).val (Pi.single 0 1)) := by rw [planeShuffle_point]
      _ = Pi.single 0 1 :=
        (Atlas.Order20160A8.Exterior.exteriorAction (planeShuffle i)).left_inv _
  · rw [Matrix.SpecialLinearGroup.coe_mul,exteriorMap_mul,LinearMap.comp_apply,
      lineChart_second y hy1 (adjacent_last y hy hys) hy]
    exact (Atlas.Order20160A8.Exterior.exteriorAction (planeShuffle i)).left_inv x

/-- Every ordered singular line is obtained from wedges 01 and 02 by the
same natural four-space actor. -/
theorem singular_line_orbit (u v : Six) (hu : pfaffian u = 0) (hv : pfaffian v = 0)
    (huv : pfaffian (u + v) = 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hne : u ≠ v) :
    ∃ g : SL(4,Bit), exteriorMap g.val (Pi.single 0 1) = u ∧
      exteriorMap g.val (Pi.single 1 1) = v := by
  obtain ⟨a,ha⟩ := singular_orbit u hu hu0
  let w := exteriorMap a⁻¹.val v
  have hw : pfaffian w = 0 := by rw [pfaffian_exteriorMap,hv,mul_zero]
  have hwu : exteriorMap a⁻¹.val u = (Pi.single 0 1 : Six) := by
    rw [←ha]
    exact (Atlas.Order20160A8.Exterior.exteriorAction a).left_inv _
  have hws : pfaffian ((Pi.single 0 1 : Six) + w) = 0 := by
    rw [←hwu,←map_add,pfaffian_exteriorMap,huv,mul_zero]
  have hw0 : w ≠ 0 := fun he => hv0
    ((Atlas.Order20160A8.Exterior.exteriorAction a⁻¹).injective (he.trans (map_zero _).symm))
  have hwn : w ≠ Pi.single 0 1 := by
    intro he
    apply hne
    exact (Atlas.Order20160A8.Exterior.exteriorAction a⁻¹).injective (hwu.trans he.symm)
  obtain ⟨b,hb0,hb1⟩ := singular_neighbour_orbit w hw hws hw0 hwn
  refine ⟨a*b,?_,?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul,exteriorMap_mul,LinearMap.comp_apply,hb0,ha]
  · rw [Matrix.SpecialLinearGroup.coe_mul,exteriorMap_mul,LinearMap.comp_apply,hb1]
    exact (Atlas.Order20160A8.Exterior.exteriorAction a).right_inv v

end Representation.BinaryParabolicExteriorSquare.SingularPresentation
