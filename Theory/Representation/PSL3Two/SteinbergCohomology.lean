module

public import Theory.Representation.PSL3Two.SmallModules
public import Theory.Representation.FirstCohomology
import Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates
import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
import Mathlib.Algebra.CharP.Pi
import Mathlib.Tactic.FinCases

/-!
# First cohomology of the binary Steinberg module

Every crossed homomorphism for the literal trace-zero adjoint action of
SL₃(F₂) is principal. Normalize its value at the order-three coordinate cycle
by subtracting a principal cocycle. The relations `a² = 1` and `(ab)⁷ = 1`
then impose six independent constraints on its eight coordinates at the
transvection `a`. An explicit vector supplies the remaining principal cocycle.
Checked words express all elementary transvections in `a,b`, so Gaussian
elimination extends equality to the whole group. No presentation-completeness
claim or projectivity hypothesis is needed.

This proves directly the first-cohomology consequence of Aschbacher–Smith,
*The Classification of Quasithin Groups*, H.6.3(1), printed p.387, combined
manuscript of 1 March 2004. It does not assert the stronger projectivity theorem.
The finite identities below are checked by Lean's kernel against the actual
group and the previously proved adjoint coordinates.
-/

public section

open Matrix Representation Representation.OneCohomology
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue
namespace BinaryLinearThree.SteinbergCohomology

private theorem coordinates_sub (u v : Steinberg) :
    coordinates (u - v) = coordinates u - coordinates v := coordinates.map_sub u v

private theorem coordinates_action (g : Group) (v : Steinberg) :
    coordinates (S g v) = (coordinateMatrix g).mulVec (coordinates v) := by
  rw [coordinateMatrix, LinearMap.toMatrix'_mulVec]
  simp

private theorem coordinates_cycle (v : Steinberg) :
    coordinates (S cycle v) = cycleMatrix.mulVec (coordinates v) := by
  rw [coordinates_action, coordinateMatrix_cycle]

private theorem coordinates_shear (v : Steinberg) :
    coordinates (S IrreducibleCatalogue.shear v) = shearMatrix.mulVec (coordinates v) := by
  rw [coordinates_action, coordinateMatrix_shear]

private theorem shear_square : IrreducibleCatalogue.shear ^ 2 = 1 := by decide +kernel
private theorem cycle_cube : cycle ^ 3 = 1 := by decide +kernel
private theorem product_seventh : (IrreducibleCatalogue.shear * cycle) ^ 7 = 1 := by decide +kernel

private theorem cocycle_one (f : cocycles S) : f.val 1 = 0 := by
  have h := f.property 1 1
  simpa using h.symm

private def geometric (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) : ℕ → Matrix (Fin 8) (Fin 8) (ZMod 2)
  | 0 => 0
  | n + 1 => M * geometric M n + 1

private theorem cocycle_power (f : cocycles S) (g : Group)
    (M : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (hM : ∀ v : Steinberg, coordinates (S g v) = M.mulVec (coordinates v)) (n : ℕ) :
    coordinates (f.val (g ^ n)) = (geometric M n).mulVec (coordinates (f.val g)) := by
  induction n with
  | zero => simp [geometric, cocycle_one]
  | succ n ih =>
    rw [pow_succ', f.property, map_add, hM, ih]
    simp [geometric, Matrix.add_mulVec, Matrix.mulVec_mulVec]

private def normMatrix : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1,0,0,1,1,0,1,0;
     0,1,1,1,0,1,0,0;
     0,1,1,1,0,1,0,0;
     1,0,0,1,1,0,1,0;
     1,0,0,1,1,0,1,0;
     1,1,1,0,1,1,1,0;
     0,0,0,0,0,0,0,0;
     0,1,1,1,0,1,0,0]

private theorem normMatrix_eq : geometric (shearMatrix * cycleMatrix) 7 = normMatrix := by
  decide +kernel

private def witness (x : Eight) : Eight := ![x 1, x 0, x 0, x 1, x 1, x 0, 0, 0]

private theorem witness_eq (x : Eight) (ha : shearMatrix.mulVec x = x)
    (hn : normMatrix.mulVec x = 0) :
    shearMatrix.mulVec (witness x) - witness x = x ∧
    cycleMatrix.mulVec (witness x) = witness x := by
  have ha0 := congrFun ha 0
  have ha1 := congrFun ha 1
  have ha6 := congrFun ha 6
  have ha5 := congrFun ha 5
  have hn0 := congrFun hn 0
  have hn1 := congrFun hn 1
  simp [shearMatrix, normMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at ha0 ha1 ha6 ha5 hn0 hn1
  have h6 : x 6 = x 0 := (CharTwo.add_eq_zero.mp (by simpa [ha1, ha5] using hn0)).symm
  have h7 : x 7 = x 0 := by
    have hh : x 0 + x 7 = 0 := by simpa [ha6, h6] using ha0
    exact (CharTwo.add_eq_zero.mp hh).symm
  have h5 : x 5 = x 1 := (CharTwo.add_eq_zero.mp (by simpa [ha6, ha1] using hn1)).symm
  constructor <;> ext i <;> fin_cases i <;>
    simp [shearMatrix, cycleMatrix, witness, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, ha6, ha1, ha5, h5, h6, h7, CharTwo.add_self_eq_zero,
      CharTwo.sub_eq_add]
  all_goals simp [add_right_comm, add_assoc, add_left_comm, CharTwo.add_self_eq_zero]

private def generator (b : Bool) : Group := if b then IrreducibleCatalogue.shear else cycle

private def wordValue (w : List Bool) : Group := (w.map generator).prod

private def elementary (i j : Fin 3) : Group :=
  if h : i = j then 1 else Matrix.SpecialLinearGroup.transvection h 1

private def elementaryWord : Fin 3 → Fin 3 → List Bool :=
  ![![[], [true], [true,false,true,false,false,true,false,true,false,false]],
    ![[false,true,false,true,false,false,true,false,true,false], [], [false,true,false,false]],
    ![[false,false,true,false], [true,false,false,true,false,true,false,false,true,false], []]]

private theorem elementary_word : ∀ i j, wordValue (elementaryWord i j) = elementary i j := by
  decide +kernel

private theorem cocycle_ext_pair (f t : cocycles S)
    (ha : f.val IrreducibleCatalogue.shear = t.val IrreducibleCatalogue.shear)
    (hb : f.val cycle = t.val cycle) : f = t := by
  have hword (w : List Bool) : f.val (wordValue w) = t.val (wordValue w) := by
    induction w with
    | nil => simp [wordValue, cocycle_one]
    | cons b bs ih =>
      change f.val (generator b * wordValue bs) = t.val (generator b * wordValue bs)
      rw [f.property, t.property, ih]
      cases b <;> simp [generator, ha, hb]
  apply Subtype.ext
  funext g
  apply SLHigherNatural.transvection_induction (fun g => f.val g = t.val g) ?_ ?_ g
  · intro i j hij c
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 from by decide) c with rfl | rfl
    · have hz : Matrix.SpecialLinearGroup.transvection hij (0 : ZMod 2) = 1 := by
        apply Subtype.ext
        simp
      simp only [hz, cocycle_one]
    · have he : elementary i j = Matrix.SpecialLinearGroup.transvection hij 1 := by
        simp [elementary, hij]
      rw [← he, ← elementary_word]
      exact hword _
  · intro a b ha hb
    rw [f.property, t.property, ha, hb]

private theorem normalize_cycle (f : cocycles S) :
    (principal S (S cycle (f.val cycle))).val cycle = f.val cycle := by
  apply coordinates.injective
  change coordinates (S cycle (S cycle (f.val cycle)) - S cycle (f.val cycle)) = _
  rw [coordinates_sub, coordinates_cycle, coordinates_cycle]
  have hc := cocycle_power f cycle cycleMatrix coordinates_cycle 3
  rw [cycle_cube, cocycle_one, map_zero] at hc
  have hnorm : cycleMatrix.mulVec (cycleMatrix.mulVec (coordinates (f.val cycle))) +
      cycleMatrix.mulVec (coordinates (f.val cycle)) + coordinates (f.val cycle) = 0 := by
    simpa [geometric, Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_add, mul_add] using hc.symm
  rw [CharTwo.sub_eq_add]
  exact CharTwo.add_eq_zero.mp hnorm

private theorem normalized_principal (f : cocycles S) (hb : f.val cycle = 0) :
    ∃ v : Steinberg, principal S v = f := by
  let x := coordinates (f.val IrreducibleCatalogue.shear)
  have ha : shearMatrix.mulVec x = x := by
    have hh := cocycle_power f IrreducibleCatalogue.shear shearMatrix coordinates_shear 2
    rw [shear_square, cocycle_one, map_zero] at hh
    exact CharTwo.add_eq_zero.mp (by
      simpa [geometric, Matrix.add_mulVec, Matrix.mulVec_mulVec] using hh.symm)
  have hn : normMatrix.mulVec x = 0 := by
    have hm (v : Steinberg) : coordinates (S (IrreducibleCatalogue.shear * cycle) v) =
        (shearMatrix * cycleMatrix).mulVec (coordinates v) := by
      rw [map_mul, Module.End.mul_apply, coordinates_shear, coordinates_cycle,
        Matrix.mulVec_mulVec]
    have hh := cocycle_power f (IrreducibleCatalogue.shear * cycle) _ hm 7
    rw [product_seventh, cocycle_one, map_zero, normMatrix_eq,
      f.property, hb, map_zero, zero_add] at hh
    exact hh.symm
  obtain ⟨hwa, hwb⟩ := witness_eq x ha hn
  refine ⟨coordinates.symm (witness x), cocycle_ext_pair _ f ?_ ?_⟩
  · apply coordinates.injective
    change coordinates (S IrreducibleCatalogue.shear _ - _) = _
    simpa only [coordinates_sub, coordinates_shear, LinearEquiv.apply_symm_apply] using hwa
  · apply coordinates.injective
    change coordinates (S cycle _ - _) = _
    simp only [coordinates_sub, coordinates_cycle, LinearEquiv.apply_symm_apply, hb, map_zero]
    exact sub_eq_zero.mpr hwb

/-- Every actual adjoint cocycle has a principal vector. -/
theorem cocycles_principal (f : cocycles S) : ∃ v : Steinberg, principal S v = f := by
  let w := S cycle (f.val cycle)
  let f₀ : cocycles S := ⟨fun g => f.val g - (principal S w).val g, by
    intro g t
    change f.val (g * t) - (principal S w).val (g * t) =
      S g (f.val t - (principal S w).val t) + (f.val g - (principal S w).val g)
    rw [f.property, (principal S w).property, (S g).map_sub]
    abel⟩
  have hb : f₀.val cycle = 0 := sub_eq_zero.mpr (normalize_cycle f).symm
  obtain ⟨v, hv⟩ := normalized_principal f₀ hb
  refine ⟨v + w, ?_⟩
  apply Subtype.ext
  funext g
  have he := congrArg (fun c : cocycles S => c.val g) hv
  change S g v - v = f.val g - (S g w - w) at he
  change S g (v + w) - (v + w) = f.val g
  rw [map_add]
  calc
    S g v + S g w - (v + w) = (S g v - v) + (S g w - w) := by abel
    _ = f.val g := by rw [he]; abel

/-- The principal-cocycle map is onto. -/
theorem principal_surjective : Function.Surjective (principal S) := cocycles_principal

/-- Pointwise form for constructing the correction to a section of an extension. -/
theorem cocycle_eq_principal (c : Group → Steinberg)
    (hc : ∀ g t, c (g * t) = S g (c t) + c g) :
    ∃ v : Steinberg, ∀ g, c g = S g v - v := by
  obtain ⟨v, hv⟩ := cocycles_principal ⟨c, hc⟩
  refine ⟨v, fun g => ?_⟩
  exact (congrArg (fun f : cocycles S => f.val g) hv).symm

/-- The literal eight-dimensional binary adjoint module has vanishing H¹. -/
theorem subsingleton_H1 : Subsingleton (H1 S) := by
  have hz (f : cocycles S) : classMap S f = 0 :=
    (classMap_eq_zero_iff S f).mpr (cocycles_principal f)
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      change classMap S a = classMap S b
      rw [hz, hz]

end BinaryLinearThree.SteinbergCohomology
