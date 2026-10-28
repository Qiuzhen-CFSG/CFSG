module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourWeyl
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MatrixTorus
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.BorelCollection

/-!
# Full torus action on the four-dimensional positive roots

Every parameter lies in the original matrix field or its actual fixed field.
The literal matrix equations imply normalization and collection of U H.
Source: Steinberg, Lectures on Chevalley Groups, Lemmas 21–24 and 64.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourTorus
open UnitaryFourFlag UnitaryFourSylow FourPositive FourWeyl
variable (E : Type*) [Field E] [CharP E 2]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "J" => form E σ hσ
local notation "K" => FixedField E σ

theorem h_A (p : torusParameters E σ) (v : E) :
    h E σ hσ p*A E σ hσ v = A E σ hσ (((p.val.1:E)/(p.val.2:E))*v)*h E σ hσ p := by
  apply Subtype.ext; apply Units.ext
  change (h E σ hσ p).val.val*(A E σ hσ v).val.val =
    (A E σ hσ _).val.val*(h E σ hσ p).val.val
  rw [h_val,A_val,A_val]
  exact Matrix4.H_A σ _ _ p.val.1.ne_zero p.val.2.ne_zero v

theorem h_C (p : torusParameters E σ) (v : E) :
    h E σ hσ p*C E σ hσ v = C E σ hσ (((p.val.1:E)*σ (p.val.2:E))*v)*h E σ hσ p := by
  apply Subtype.ext; apply Units.ext
  change (h E σ hσ p).val.val*(C E σ hσ v).val.val =
    (C E σ hσ _).val.val*(h E σ hσ p).val.val
  rw [h_val,C_val,C_val]
  exact Matrix4.H_C σ hσ _ _ p.val.1.ne_zero p.val.2.ne_zero v

theorem h_B (p : torusParameters E σ) (v : K) :
    h E σ hσ p*B E σ hσ v =
      B E σ hσ (normParameter E σ hσ (p.val.2:E) v)*h E σ hσ p := by
  apply Subtype.ext; apply Units.ext
  change (h E σ hσ p).val.val*(B E σ hσ v).val.val =
    (B E σ hσ _).val.val*(h E σ hσ p).val.val
  rw [h_val,B_val,B_val]
  exact Matrix4.H_B σ _ _ p.val.1.ne_zero p.val.2.ne_zero (v:E)

theorem h_D (p : torusParameters E σ) (v : K) :
    h E σ hσ p*D E σ hσ v =
      D E σ hσ (normParameter E σ hσ (p.val.1:E) v)*h E σ hσ p := by
  apply Subtype.ext; apply Units.ext
  change (h E σ hσ p).val.val*(D E σ hσ v).val.val =
    (D E σ hσ _).val.val*(h E σ hσ p).val.val
  rw [h_val,D_val,D_val]
  exact Matrix4.H_D σ _ _ p.val.1.ne_zero p.val.2.ne_zero (v:E)

/-- The full model torus supplies all four normalization equations. -/
theorem torusLaws : (roots E σ hσ).TorusLaws (hHom E σ hσ) where
  A p a := by
    refine ⟨Multiplicative.ofAdd (((p.val.1:E)/(p.val.2:E))*a.toAdd),?_⟩
    change h E σ hσ p*A E σ hσ a.toAdd*(h E σ hσ p)⁻¹=_
    rw [h_A,mul_assoc,mul_inv_cancel,mul_one]
    rfl
  D p d := by
    refine ⟨Multiplicative.ofAdd (normParameter E σ hσ (p.val.1:E) d.toAdd),?_⟩
    change h E σ hσ p*D E σ hσ d.toAdd*(h E σ hσ p)⁻¹=_
    rw [h_D,mul_assoc,mul_inv_cancel,mul_one]
    rfl
  C p c := by
    refine ⟨Multiplicative.ofAdd (((p.val.1:E)*σ (p.val.2:E))*c.toAdd),?_⟩
    change h E σ hσ p*C E σ hσ c.toAdd*(h E σ hσ p)⁻¹=_
    rw [h_C,mul_assoc,mul_inv_cancel,mul_one]
    rfl
  B p b := by
    refine ⟨Multiplicative.ofAdd (normParameter E σ hσ (p.val.2:E) b.toAdd),?_⟩
    change h E σ hσ p*B E σ hσ b.toAdd*(h E σ hσ p)⁻¹=_
    rw [h_B,mul_assoc,mul_inv_cancel,mul_one]
    rfl

/-- Every model root-and-torus word has ordered positive coordinates. -/
theorem borel_collected {g : SU E J} (hg : g∈(roots E σ hσ).borel (hHom E σ hσ)) :
    ∃ a d c b k, g=(roots E σ hσ).word a d c b*hHom E σ hσ k :=
  (torusLaws E σ hσ).exists_word (collects E σ hσ) hg

end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourTorus
