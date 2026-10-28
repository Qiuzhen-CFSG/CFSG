module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveWeyl
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MatrixTorus
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.BorelCollection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Full torus action on the general five-dimensional Hermitian roots

The anisotropic middle scalar has norm one. Scaling a Hermitian root by
(k/delta, norm(k)) therefore preserves its trace equation. These actual model
actions instantiate the positive-root normalization and U H collection.
Source: Steinberg, Lectures on Chevalley Groups, Lemmas 21–24 and 63–64.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveTorus
open FivePositive FiveWeyl
variable {E : Type*} [Field E] [CharP E 2]
variable (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)

omit [CharP E 2] in
theorem delta_norm (p : Eˣ × Eˣ) :
    Matrix5.delta J.conj p.1 p.2*J.conj (Matrix5.delta J.conj p.1 p.2)=1 := by
  simp [Matrix5.delta,map_div₀,map_mul]

/-- Root scaling, with the determinant-correcting middle entry retained. -/
def scale (p : Eˣ × Eˣ) (k : E) (v : Parameter J) : Parameter J :=
  ⟨((k/Matrix5.delta J.conj p.1 p.2)*v.val.1,(k*J.conj k)*v.val.2),by
    have hd := delta_norm J p
    have hdz : Matrix5.delta J.conj p.1 p.2≠0 := by
      intro hz
      rw [hz,zero_mul] at hd
      exact zero_ne_one hd
    change (k*J.conj k)*v.val.2+J.conj ((k*J.conj k)*v.val.2)+
      ((k/Matrix5.delta J.conj p.1 p.2)*v.val.1)*
        J.conj ((k/Matrix5.delta J.conj p.1 p.2)*v.val.1)=0
    simp only [map_mul,map_div₀,J.conj_involutive k]
    have he : (k/Matrix5.delta J.conj p.1 p.2)*
        (J.conj k/J.conj (Matrix5.delta J.conj p.1 p.2))=k*J.conj k := by
      rw [div_mul_div_comm,hd,div_one]
    calc
      _ = k*J.conj k*(v.val.2+J.conj v.val.2)+
          ((k/Matrix5.delta J.conj p.1 p.2)*(J.conj k/J.conj (Matrix5.delta J.conj p.1 p.2)))*
            (v.val.1*J.conj v.val.1) := by ring
      _ = k*J.conj k*(v.val.2+J.conj v.val.2+v.val.1*J.conj v.val.1) := by rw [he]; ring
      _ = 0 := by rw [v.property,mul_zero]⟩

theorem h_A (p : Eˣ × Eˣ) (v : E) :
    h J κ hκ hJ p*A J κ hκ hJ v =
      A J κ hκ hJ (((p.1:E)/(p.2:E))*v)*h J κ hκ hJ p := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_h,evaluate_A]
  exact Matrix5.H_A J.conj _ _ p.1.ne_zero p.2.ne_zero v

theorem h_C (p : Eˣ × Eˣ) (v : E) :
    h J κ hκ hJ p*C J hJ v =
      C J hJ (((p.1:E)*J.conj (p.2:E))*v)*h J κ hκ hJ p := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_h,evaluate_C]
  exact Matrix5.H_C J.conj J.conj_involutive _ _ p.1.ne_zero p.2.ne_zero v

theorem h_B (p : Eˣ × Eˣ) (v : Parameter J) :
    h J κ hκ hJ p*B J hJ v =
      B J hJ (scale J p p.2 v)*h J κ hκ hJ p := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_h,evaluate_B]
  exact Matrix5.H_B J.conj J.conj_involutive _ _ p.1.ne_zero p.2.ne_zero _ _

theorem h_D (p : Eˣ × Eˣ) (v : Parameter J) :
    h J κ hκ hJ p*D J hJ v =
      D J hJ (scale J p p.1 v)*h J κ hκ hJ p := by
  apply evaluate_injective J κ
  simp only [map_mul,evaluate_h,evaluate_D]
  exact Matrix5.H_D J.conj J.conj_involutive _ _ p.1.ne_zero p.2.ne_zero _ _

/-- The full model torus normalizes all four positive parameter groups. -/
theorem torusLaws : (roots J κ hκ hJ).TorusLaws (h J κ hκ hJ) where
  A p a := by
    refine ⟨Multiplicative.ofAdd (((p.1:E)/(p.2:E))*a.toAdd),?_⟩
    change h J κ hκ hJ p*A J κ hκ hJ a.toAdd*(h J κ hκ hJ p)⁻¹=_
    rw [h_A,mul_assoc,mul_inv_cancel,mul_one]
    rfl
  D p d := by
    refine ⟨scale J p p.1 d,?_⟩
    change h J κ hκ hJ p*D J hJ d*(h J κ hκ hJ p)⁻¹=_
    rw [h_D,mul_assoc,mul_inv_cancel,mul_one]
    rfl
  C p c := by
    refine ⟨Multiplicative.ofAdd (((p.1:E)*J.conj (p.2:E))*c.toAdd),?_⟩
    change h J κ hκ hJ p*C J hJ c.toAdd*(h J κ hκ hJ p)⁻¹=_
    rw [h_C,mul_assoc,mul_inv_cancel,mul_one]
    rfl
  B p b := by
    refine ⟨scale J p p.2 b,?_⟩
    change h J κ hκ hJ p*B J hJ b*(h J κ hκ hJ p)⁻¹=_
    rw [h_B,mul_assoc,mul_inv_cancel,mul_one]
    rfl

/-- General-q ordered root-and-torus collection in the actual SU₅ carrier. -/
theorem borel_collected {g : J.specialSubgroup} (hg : g∈(roots J κ hκ hJ).borel (h J κ hκ hJ)) :
    ∃ a d c b k, g=(roots J κ hκ hJ).word a d c b*h J κ hκ hJ k :=
  (torusLaws J κ hκ hJ).exists_word (collects J κ hκ hJ) hg

end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FiveTorus
