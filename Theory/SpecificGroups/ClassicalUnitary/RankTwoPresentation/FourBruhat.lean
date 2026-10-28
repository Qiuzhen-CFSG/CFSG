module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourWeyl
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.MatrixRankOne
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.RankOneCollection
import Mathlib.Tactic.Group

/-!
# Rank-one Bruhat equations in the literal SU₄ model

The reciprocal parameters lie in the full fixed-product torus. The resulting
reflection laws instantiate the abstract positive-word two-cell argument,
including the field of order two. No simplicity or faithfulness is assumed.
Source: Steinberg, Lectures on Chevalley Groups, Lemma 24 and Lemma 64.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourBruhat
open UnitaryFourFlag UnitaryFourSylow FourPositive FourWeyl
variable (E : Type*) [Field E] [Finite E] [CharP E 2]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "J" => form E σ hσ
local notation "K" => FixedField E σ

def aTorus (v : E) (hv : v≠0) : torusParameters E σ :=
  ⟨((Units.mk0 v hv)⁻¹,Units.mk0 v hv),by
    change σ (↑((Units.mk0 v hv)⁻¹)*v)=↑((Units.mk0 v hv)⁻¹)*v
    simp [hv]⟩

def bTorus (v : K) (hv : v≠0) : torusParameters E σ :=
  ⟨(1,(Units.mk0 (v:E) (by exact_mod_cast hv))⁻¹),by
    change σ ((1:E)*↑((Units.mk0 (v:E) _)⁻¹))=(1:E)*↑((Units.mk0 (v:E) _)⁻¹)
    simp [show σ (v:E)=(v:E) from v.property]⟩

theorem s_A (v : E) (hv : v≠0) :
    s E σ hσ*A E σ hσ v*s E σ hσ =
      A E σ hσ v⁻¹*h E σ hσ (aTorus E σ v hv)*s E σ hσ*A E σ hσ v⁻¹ := by
  apply Subtype.ext; apply Units.ext
  change (s E σ hσ).val.val*(A E σ hσ v).val.val*(s E σ hσ).val.val =
    (A E σ hσ v⁻¹).val.val*(h E σ hσ _).val.val*(s E σ hσ).val.val*(A E σ hσ v⁻¹).val.val
  rw [s_val,A_val,A_val,h_val]
  simpa only [aTorus,Units.val_inv_eq_inv_val,Units.val_mk0] using Matrix4.S_A_bruhat σ v hv

theorem t_B (v : K) (hv : v≠0) :
    t E σ hσ*B E σ hσ v*t E σ hσ =
      B E σ hσ v⁻¹*h E σ hσ (bTorus E σ v hv)*t E σ hσ*B E σ hσ v⁻¹ := by
  apply Subtype.ext; apply Units.ext
  change (t E σ hσ).val.val*(B E σ hσ v).val.val*(t E σ hσ).val.val =
    (B E σ hσ v⁻¹).val.val*(h E σ hσ _).val.val*(t E σ hσ).val.val*(B E σ hσ v⁻¹).val.val
  rw [t_val,B_val,B_val,h_val]
  simpa only [bTorus,Units.val_inv_eq_inv_val,Units.val_mk0,Units.val_one,Subfield.coe_inv] using
    Matrix4.T_B_bruhat σ (v:E) (by exact_mod_cast hv) v.property

private theorem involution_transport {G : Type*} [Group G] (w x y : G)
    (hw : w^2=1) (he : w*x*w=y) : w*y*w=x := by
  have hww : w*w=1 := by simpa only [pow_two] using hw
  rw [←he]
  calc
    w*(w*x*w)*w=(w*w)*x*(w*w) := by simp only [mul_assoc]
    _ = x := by rw [hww,one_mul,mul_one]

/-- All six transported roots and both rank-one alternatives hold in the model. -/
theorem reflectionLaws : ReflectionLaws (roots E σ hσ) (hHom E σ hσ) (s E σ hσ) (t E σ hσ) where
  ss := by simpa only [pow_two] using s_sq E σ hσ
  tt := by simpa only [pow_two] using t_sq E σ hσ
  sD d := ⟨d,involution_transport _ _ _ (s_sq E σ hσ) (s_B E σ hσ d.toAdd)⟩
  sC c := ⟨Multiplicative.ofAdd (σ c.toAdd),s_C E σ hσ c.toAdd⟩
  sB b := ⟨b,s_B E σ hσ b.toAdd⟩
  tA a := ⟨Multiplicative.ofAdd a.toAdd,t_A E σ hσ a.toAdd⟩
  tD d := ⟨d,t_D E σ hσ d.toAdd⟩
  tC c := ⟨Multiplicative.ofAdd c.toAdd,
    involution_transport _ _ _ (t_sq E σ hσ) (t_A E σ hσ c.toAdd)⟩
  sA a := by
    by_cases ha : a=1
    · left; subst a
      simp only [map_one,mul_one]
      simpa only [pow_two] using s_sq E σ hσ
    · right
      have hv : a.toAdd≠0 := by simpa using ha
      exact ⟨Multiplicative.ofAdd a.toAdd⁻¹,aTorus E σ a.toAdd hv,
        Multiplicative.ofAdd a.toAdd⁻¹,s_A E σ hσ a.toAdd hv⟩
  tB b := by
    by_cases hb : b=1
    · left; subst b
      simp only [map_one,mul_one]
      simpa only [pow_two] using t_sq E σ hσ
    · right
      have hv : b.toAdd≠0 := by simpa using hb
      exact ⟨Multiplicative.ofAdd b.toAdd⁻¹,bTorus E σ b.toAdd hv,
        Multiplicative.ofAdd b.toAdd⁻¹,t_B E σ hσ b.toAdd hv⟩

end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourBruhat
