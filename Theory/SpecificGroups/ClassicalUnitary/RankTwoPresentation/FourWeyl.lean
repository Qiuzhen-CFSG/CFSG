module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourPositive
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MatrixWeyl
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourCartan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Full diagonal and marked Weyl generators in the unitary four-space

The two diagonal parameters obey exactly the determinant-one fixed-product
condition. The root parameter convention is that of `FourPositive`.
Source: Steinberg, Lectures on Chevalley Groups, Theorem 33 and Lemmas 63–64.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourWeyl
open UnitaryFourFlag UnitaryFourGeneration UnitaryFourSylow SmallCompletion FourPositive
variable (E : Type*) [Field E] [CharP E 2] [Finite E]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "J" => form E σ hσ

/-- The full determinant-one torus parameter group. -/
def torusParameters : Subgroup (Eˣ × Eˣ) where
  carrier := {p | σ ((p.1:E)*(p.2:E))=(p.1:E)*(p.2:E)}
  one_mem' := by simp
  mul_mem' := by
    intro p q hp hq
    change σ (((p.1:E)*(q.1:E))*((p.2:E)*(q.2:E))) = ((p.1:E)*(q.1:E))*((p.2:E)*(q.2:E))
    calc
      _ = σ ((p.1:E)*(p.2:E))*σ ((q.1:E)*(q.2:E)) := by rw [←map_mul]; congr 1; ring
      _ = _ := by rw [hp,hq]; ring
  inv_mem' := by
    intro p hp
    change σ ((↑(p.1⁻¹):E)*(↑(p.2⁻¹):E))=(↑(p.1⁻¹):E)*(↑(p.2⁻¹):E)
    simpa only [Units.val_inv_eq_inv_val,←mul_inv,map_inv₀] using congrArg Inv.inv hp

omit [CharP E 2] [Finite E] in
private theorem h_det (p : torusParameters E σ) :
    (Matrix4.H σ p.val.1 p.val.2).det=1 := by
  have hp := p.property
  change σ ((p.val.1:E)*(p.val.2:E))=(p.val.1:E)*(p.val.2:E) at hp
  simp only [map_mul] at hp
  simp [Matrix4.H,Matrix.det_diagonal,Fin.prod_univ_succ]
  field_simp
  linear_combination -hp

/-- The full torus, with its literal determinant-one diagonal matrix. -/
def h (p : torusParameters E σ) : SU E J :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (Matrix4.H σ p.val.1 p.val.2)
      (by rw [h_det E σ p]; exact one_ne_zero),by
    change (form E σ hσ).conjTranspose (Matrix4.H σ p.val.1 p.val.2) * gram E *
      Matrix4.H σ p.val.1 p.val.2 = gram E
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix4.H,form,gram,HermitianForm.conjTranspose,Matrix.mul_apply,
        Fin.sum_univ_succ,hσ (p.val.1:E),hσ (p.val.2:E)],
    by apply Units.ext; exact h_det E σ p⟩

omit [CharP E 2] [Finite E] in
theorem h_val (p : torusParameters E σ) :
    (h E σ hσ p).val.val=Matrix4.H σ p.val.1 p.val.2 := rfl

def hHom : torusParameters E σ →* SU E J where
  toFun := h E σ hσ
  map_one' := by
    apply Subtype.ext; apply Units.ext
    rw [h_val]
    exact Matrix4.H_one σ
  map_mul' p q := by
    apply Subtype.ext; apply Units.ext
    change (h E σ hσ (p*q)).val.val=(h E σ hσ p).val.val*(h E σ hσ q).val.val
    rw [h_val,h_val,h_val]
    exact (Matrix4.H_mul σ _ _ _ _).symm

omit [CharP E 2] [Finite E] in
theorem h_injective : Function.Injective (h E σ hσ) := by
  intro p q he
  have hm := congrArg (fun g : SU E J => g.val.val) he
  rw [h_val,h_val] at hm
  have he : ((p.val.1:E),(p.val.2:E))=((q.val.1:E),(q.val.2:E)) := Matrix4.H_injective σ hm
  apply Subtype.ext
  apply Prod.ext
  · exact Units.ext (congrArg Prod.fst he)
  · exact Units.ext (congrArg Prod.snd he)


def s : SU E J := pairSwap E σ hσ
def t : SU E J := middleSwap E σ hσ

theorem s_val : (s E σ hσ).val.val=Matrix4.S := rfl
theorem t_val : (t E σ hσ).val.val=Matrix4.T := rfl

theorem s_sq : s E σ hσ ^ 2=1 := FourCartan.pairSwap_sq E σ hσ
theorem t_sq : t E σ hσ ^ 2=1 := FourCartan.middleSwap_sq E σ hσ

theorem st_four : (s E σ hσ*t E σ hσ)^4=1 := by
  apply Subtype.ext; apply Units.ext
  change ((s E σ hσ).val.val*(t E σ hσ).val.val)^4=1
  rw [s_val,t_val]
  exact Matrix4.ST_four E

theorem s_B (b : FixedField E σ) :
    s E σ hσ * B E σ hσ b * s E σ hσ = D E σ hσ b := by
  apply Subtype.ext; apply Units.ext
  change (s E σ hσ).val.val*(B E σ hσ b).val.val*(s E σ hσ).val.val=(D E σ hσ b).val.val
  rw [s_val,B_val,D_val]
  exact Matrix4.S_B _

theorem s_C (c : E) :
    s E σ hσ * C E σ hσ c * s E σ hσ = C E σ hσ (σ c) := by
  apply Subtype.ext; apply Units.ext
  change (s E σ hσ).val.val*(C E σ hσ c).val.val*(s E σ hσ).val.val=(C E σ hσ (σ c)).val.val
  rw [s_val,C_val,C_val]
  exact Matrix4.S_C σ hσ _

theorem t_A (a : E) :
    t E σ hσ * A E σ hσ a * t E σ hσ = C E σ hσ a := by
  apply Subtype.ext; apply Units.ext
  change (t E σ hσ).val.val*(A E σ hσ a).val.val*(t E σ hσ).val.val=(C E σ hσ a).val.val
  rw [t_val,A_val,C_val]
  exact Matrix4.T_A σ _

theorem t_D (d : FixedField E σ) :
    t E σ hσ * D E σ hσ d * t E σ hσ = D E σ hσ d := by
  apply Subtype.ext; apply Units.ext
  change (t E σ hσ).val.val*(D E σ hσ d).val.val*(t E σ hσ).val.val=(D E σ hσ d).val.val
  rw [t_val,D_val]
  exact Matrix4.T_D _

end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourWeyl
