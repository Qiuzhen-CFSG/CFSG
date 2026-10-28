module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveWeyl
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveRootGeneration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Hermitian coordinates for unitary rank-two elimination

The single basis permutation used by the presentation preserves the exact
Hermitian pairing, determinant and both literal flag stabilizers. Diagonal
special-unitary matrices are precisely the two-parameter torus: unitarity
fixes the final two entries and determinant one fixes the middle entry.
These general-parameter calculations feed the whole-SU₅ generation proof.
Source: Steinberg, Lectures on Chevalley Groups, Theorem 33 and Lemmas 63–64.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveCoordinates
open FivePositive FiveWeyl
open Theory.SpecificGroups.UnitaryFive PlaneCore SmallCompletion FivePaths
variable {E : Type*} [Field E] [CharP E 2]
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)

def pair (v w : Fin 5 → E) : E :=
  J.conj (v 0)*w 4+J.conj (v 1)*w 3+J.conj (v 2)*w 2+
    J.conj (v 3)*w 1+J.conj (v 4)*w 0

theorem evaluate_apply (g : J.specialSubgroup) (i j : Fin 5) :
    evaluate J κ g i j=(coordinates J κ g).val (orderSwap i) (orderSwap j) := rfl

include hκ hJ in
theorem pair_columns (g : J.specialSubgroup) (i j : Fin 5) :
    pair J (fun k => evaluate J κ g k i) (fun k => evaluate J κ g k j)=
      if i.rev=j then 1 else 0 := by
  let M := (coordinates J κ g).val
  have hu : J.conjTranspose M*planeGram*M=planeGram :=
    FiveCartan.coordinates_preserves J κ hκ hJ g
  have he : ∀ a b, J.conj (M 3 a)*M 0 b+J.conj (M 4 a)*M 1 b+
      J.conj (M 2 a)*M 2 b+J.conj (M 0 a)*M 3 b+J.conj (M 1 a)*M 4 b=
      (planeGram : Matrix (Fin 5) (Fin 5) E) a b := by
    intro a b
    have hh := congrArg (fun N : Matrix (Fin 5) (Fin 5) E => N a b) hu
    simpa [HermitianForm.conjTranspose,Matrix.mul_apply,Fin.sum_univ_succ,planeGram,
      add_assoc] using hh
  calc
    _ = (planeGram : Matrix (Fin 5) (Fin 5) E) (orderSwap i) (orderSwap j) := by
      rw [←he]
      change J.conj (M 0 (orderSwap i))*M 3 (orderSwap j)+
        J.conj (M 1 (orderSwap i))*M 4 (orderSwap j)+
        J.conj (M 2 (orderSwap i))*M 2 (orderSwap j)+
        J.conj (M 4 (orderSwap i))*M 1 (orderSwap j)+
        J.conj (M 3 (orderSwap i))*M 0 (orderSwap j)=_
      ring
    _ = _ := by fin_cases i <;> fin_cases j <;> rfl

theorem evaluate_det (g : J.specialSubgroup) : (evaluate J κ g).det=1 := by
  change (Matrix.reindex orderSwap orderSwap (coordinates J κ g).val).det=1
  rw [Matrix.det_reindex_self]
  exact FiveCartan.coordinates_det J κ g

theorem column_ne_zero (g : J.specialSubgroup) (j : Fin 5) :
    (fun i => evaluate J κ g i j)≠0 := by
  intro hz
  have he := congrArg (fun M : Matrix (Fin 5) (Fin 5) E => M j j)
    ((evaluate J κ).map_mul g⁻¹ g)
  rw [inv_mul_cancel,map_one] at he
  have hj (i : Fin 5) : evaluate J κ g i j=0 := congrFun hz i
  simp [Matrix.mul_apply,hj] at he

theorem mem_line_iff [Finite E] (g : J.specialSubgroup) :
    g∈specialStabilizer J (line E) ↔ ∀ i, i≠0 → evaluate J κ g i 0=0 := by
  rw [FiveFixed.mem_line_iff J κ]
  constructor <;> intro hh i hi
  · change (coordinates J κ g).val (orderSwap i) (orderSwap 0)=0
    apply hh
    fin_cases i <;> simp_all [orderSwap,Equiv.swap_apply_def]
  · have h := hh (orderSwap i) (by
      fin_cases i <;> simp_all [orderSwap,Equiv.swap_apply_def])
    simpa only [evaluate_apply,orderSwap,Equiv.swap_apply_self,show Equiv.swap (3:Fin 5) 4 0=0 from rfl] using h

theorem mem_plane_iff [Finite E] (g : J.specialSubgroup) :
    g∈specialStabilizer J (plane E) ↔
      ∀ i j, (i=2 ∨ i=3 ∨ i=4) → (j=0 ∨ j=1) → evaluate J κ g i j=0 := by
  rw [FiveFixed.mem_plane_iff J κ]
  constructor <;> intro hh i j hi hj
  · change (coordinates J κ g).val (orderSwap i) (orderSwap j)=0
    apply hh <;> rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl <;>
      simp [orderSwap,Equiv.swap_apply_def]
  · have h := hh (orderSwap i) (orderSwap j) (by
      rcases hi with rfl|rfl|rfl <;> simp [orderSwap,Equiv.swap_apply_def]) (by
      rcases hj with rfl|rfl <;> simp [orderSwap,Equiv.swap_apply_def])
    simpa only [evaluate_apply,orderSwap,Equiv.swap_apply_self,show Equiv.swap (3:Fin 5) 4 0=0 from rfl] using h

include hκ hJ in
theorem diagonal_in_torus (g : J.specialSubgroup) (hg : FiveDiagonal.IsDiagonal J κ g) :
    g∈(h J κ hκ hJ).range := by
  obtain ⟨d,hd⟩ := hg
  have hm : evaluate J κ g=diagonal (fun i => d (orderSwap i)) := by
    change Matrix.reindexRingEquiv E orderSwap (coordinates J κ g).val=_
    rw [hd]
    ext i j
    simp [Matrix.reindexRingEquiv,Matrix.reindex,Matrix.diagonal_apply,orderSwap]
  let v : Fin 5 → E := fun i => d (orderSwap i)
  have hu := pair_columns J κ hκ hJ g
  rw [hm] at hu
  have h04 : J.conj (v 0)*v 4=1 := by simpa [pair,v] using hu 0 4
  have h13 : J.conj (v 1)*v 3=1 := by simpa [pair,v] using hu 1 3
  have h0 : v 0≠0 := by intro he; simp [he] at h04
  have h1 : v 1≠0 := by intro he; simp [he] at h13
  have h4 : v 4=(J.conj (v 0))⁻¹ := eq_inv_of_mul_eq_one_right h04
  have h3 : v 3=(J.conj (v 1))⁻¹ := eq_inv_of_mul_eq_one_right h13
  have hdg := evaluate_det J κ g
  rw [hm] at hdg
  have hdg' : v 0*v 1*v 2*v 3*v 4=1 := by
    simpa [Matrix.det_diagonal,Fin.prod_univ_succ,v,mul_assoc] using hdg
  have h2 : v 2=Matrix5.delta J.conj (v 0) (v 1) := by
    rw [h4,h3] at hdg'
    dsimp [Matrix5.delta]
    apply (eq_div_iff (mul_ne_zero h0 h1)).mpr
    have h0' : J.conj (v 0)≠0 := (map_ne_zero J.conj).mpr h0
    have h1' : J.conj (v 1)≠0 := (map_ne_zero J.conj).mpr h1
    field_simp at hdg'
    rw [map_mul]
    linear_combination hdg'
  refine ⟨(Units.mk0 (v 0) h0,Units.mk0 (v 1) h1),?_⟩
  apply evaluate_injective J κ
  rw [evaluate_h,hm]
  change Matrix5.H J.conj (v 0) (v 1)=diagonal v
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix5.H,h2,h3,h4]
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveCoordinates
