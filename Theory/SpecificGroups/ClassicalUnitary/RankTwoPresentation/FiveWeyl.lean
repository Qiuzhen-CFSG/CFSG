module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePositive
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MatrixWeyl
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Full diagonal and marked Weyl generators in the actual unitary five-space

The torus is parametrized by two independent units of the matrix field.
The determinant-correcting middle entry and the single basis permutation
are retained. All relations below are in the existing SU₅ carrier.
Source: Steinberg, Lectures on Chevalley Groups, Theorem 33 and Lemmas 63–64.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveWeyl
open Theory.SpecificGroups.UnitaryFive
open PlaneCore SmallCompletion FivePaths FiveRoots FivePositive
variable {E : Type*} [Field E] [CharP E 2]
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)

def diagonalHom : Eˣ × Eˣ →* GL (Fin 2) E where
  toFun p :=
    { val := Matrix.diagonal ![(p.1:E),(p.2:E)]
      inv := Matrix.diagonal ![(p.1:E)⁻¹,(p.2:E)⁻¹]
      val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
      inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp }
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' p q := by
    apply Units.ext
    change Matrix.diagonal ![((p*q).1:E),((p*q).2:E)] =
      Matrix.diagonal ![(p.1:E),(p.2:E)] * Matrix.diagonal ![(q.1:E),(q.2:E)]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> rfl

omit [CharP E 2] in
private theorem diagonalHom_inv_val (p : Eˣ × Eˣ) :
    (diagonalHom p).inv = Matrix.diagonal ![(p.1:E)⁻¹,(p.2:E)⁻¹] := rfl

/-- The entire determinant-one diagonal torus, including the middle correction. -/
def h : Eˣ × Eˣ →* J.specialSubgroup :=
  (planeLeviSU J κ hκ hJ).comp diagonalHom

def s : J.specialSubgroup := pairSwap J κ hκ hJ
def t : J.specialSubgroup := middleSwap J κ hκ hJ

theorem evaluate_h (p : Eˣ × Eˣ) :
    evaluate J κ (h J κ hκ hJ p)=Matrix5.H J.conj p.1 p.2 := by
  change Matrix.reindexRingEquiv E orderSwap
    ((coordinates J κ (planeLeviSU J κ hκ hJ (diagonalHom p))).val)=_
  rw [coordinates_levi]
  change Matrix.reindexRingEquiv E orderSwap (planeBlockMatrix J (diagonalHom p)) = _
  simp only [planeBlockMatrix,diagonalHom_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindexRingEquiv,Matrix.reindex,orderSwap,Equiv.swap_apply_def,
      planeMiddleScalar,planeAdjoint,diagonalHom,
      Matrix5.H,Matrix5.delta,div_eq_mul_inv]

theorem evaluate_s : evaluate J κ (s J κ hκ hJ)=Matrix5.S := by
  change Matrix.reindexRingEquiv E orderSwap ((coordinates J κ (pairSwap J κ hκ hJ)).val)=_
  rw [coordinates_pairSwap,pair_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindexRingEquiv,Matrix.reindex,orderSwap,Equiv.swap_apply_def,Matrix5.S]

theorem evaluate_t : evaluate J κ (t J κ hκ hJ)=Matrix5.T := by
  change Matrix.reindexRingEquiv E orderSwap ((coordinates J κ (middleSwap J κ hκ hJ)).val)=_
  rw [coordinates_middleSwap,middle_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindexRingEquiv,Matrix.reindex,orderSwap,Equiv.swap_apply_def,Matrix5.T]

theorem h_injective : Function.Injective (h J κ hκ hJ) := by
  intro p q he
  have hm := congrArg (evaluate J κ) he
  rw [evaluate_h,evaluate_h] at hm
  have he : ((p.1:E),(p.2:E))=((q.1:E),(q.2:E)) := Matrix5.H_injective J.conj hm
  apply Prod.ext
  · exact Units.ext (congrArg Prod.fst he)
  · exact Units.ext (congrArg Prod.snd he)

theorem s_sq : s J κ hκ hJ ^ 2=1 := pairSwap_sq J κ hκ hJ

theorem t_sq : t J κ hκ hJ ^ 2=1 := middleSwap_sq J κ hκ hJ

theorem st_four : (s J κ hκ hJ*t J κ hκ hJ)^4=1 := by
  apply evaluate_injective J κ
  simp only [map_pow,map_mul,map_one,evaluate_s,evaluate_t]
  exact Matrix5.ST_four E

theorem s_h (p : Eˣ × Eˣ) :
    s J κ hκ hJ * h J κ hκ hJ p * s J κ hκ hJ = h J κ hκ hJ (p.2,p.1) := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_s,evaluate_h]
  exact Matrix5.S_H J.conj _ _

theorem t_h (p : Eˣ × Eˣ) :
    t J κ hκ hJ * h J κ hκ hJ p * t J κ hκ hJ =
      h J κ hκ hJ (p.1,(Units.map J.conj.toMonoidHom p.2)⁻¹) := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_t,evaluate_h]
  simp only [Units.val_inv_eq_inv_val,Units.coe_map]
  exact Matrix5.T_H J.conj J.conj_involutive (p.1:E) (p.2:E)

theorem s_B (p : Parameter J) :
    s J κ hκ hJ * B J hJ p * s J κ hκ hJ = D J hJ p := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_s,evaluate_B,evaluate_D]
  exact Matrix5.S_B J.conj _ _

theorem s_C (c : E) :
    s J κ hκ hJ * C J hJ c * s J κ hκ hJ = C J hJ (J.conj c) := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_s,evaluate_C]
  exact Matrix5.S_C J.conj J.conj_involutive _

theorem t_A (a : E) :
    t J κ hκ hJ * A J κ hκ hJ a * t J κ hκ hJ = C J hJ a := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_t,evaluate_A,evaluate_C]
  exact Matrix5.T_A J.conj _

theorem t_D (p : Parameter J) :
    t J κ hκ hJ * D J hJ p * t J κ hκ hJ = D J hJ p := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_t,evaluate_D]
  exact Matrix5.T_D J.conj _ _

end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveWeyl
