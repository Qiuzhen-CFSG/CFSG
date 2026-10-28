module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.Presentation
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.ModelSeparation

/-!
# FourPresentation

The explicit field and fixed-field formulas instantiate every relation of
the abstract presentation. Matrix Borel coordinates and Weyl pivots prove
that its canonical evaluation in SU₄ is injective. No model homomorphism or
faithfulness is assumed. The full-model generation module supplies its
surjectivity. Source: Steinberg, Lectures on Chevalley Groups, Lemmas 21–26,
Theorem 33 and Lemma 64; the literal matrices fix all conventions.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourPresentation
open UnitaryFourFlag UnitaryFourSylow FourPositive FourWeyl
variable (E : Type*) [Field E] [Finite E] [CharP E 2]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "J" => form E σ hσ
local notation "K" => FixedField E σ

def parameters : Presentation.Parameters (Multiplicative E) (Multiplicative K)
    (Multiplicative E) (Multiplicative K) (torusParameters E σ) where
  ca c a := Multiplicative.ofAdd (traceParameter E σ hσ a.toAdd c.toAdd)
  bd _ _ := 1
  baD b a := Multiplicative.ofAdd (normParameter E σ hσ a.toAdd b.toAdd)
  baC b a := Multiplicative.ofAdd (a.toAdd*(b.toAdd:E))
  hA k a := Multiplicative.ofAdd (((k.val.1:E)/(k.val.2:E))*a.toAdd)
  hD k d := Multiplicative.ofAdd (normParameter E σ hσ k.val.1 d.toAdd)
  hC k c := Multiplicative.ofAdd (((k.val.1:E)*σ (k.val.2:E))*c.toAdd)
  hB k b := Multiplicative.ofAdd (normParameter E σ hσ k.val.2 b.toAdd)
  sh := FourCells.swapParameter E σ
  th := FourCells.turnParameter E σ hσ
  sD := id
  sC c := Multiplicative.ofAdd (σ c.toAdd)
  sB := id
  tA := id
  tD := id
  tC := id
  rankA a ha := (Multiplicative.ofAdd a.toAdd⁻¹,
    FourBruhat.aTorus E σ a.toAdd (by simpa using ha),Multiplicative.ofAdd a.toAdd⁻¹)
  rankB b hb := (Multiplicative.ofAdd b.toAdd⁻¹,
    FourBruhat.bTorus E σ b.toAdd (by simpa using hb),Multiplicative.ofAdd b.toAdd⁻¹)

def modelGenerators := Presentation.Generator.ofMaps (roots E σ hσ) (hHom E σ hσ) (s E σ hσ) (t E σ hσ)

private theorem flip {G : Type*} [Group G] {w x y : G} (hw : w*w=1) (he : w*x*w=y) : w*y*w=x := by
  rw [←he]
  calc
    w*(w*x*w)*w=(w*w)*x*(w*w) := by simp only [mul_assoc]
    _ = x := by rw [hw,one_mul,mul_one]

theorem model_satisfies : (parameters E σ hσ).Satisfies (modelGenerators E σ hσ) := by
  intro x y he
  cases he <;> simp only [Presentation.a,Presentation.d,Presentation.c,Presentation.b,
    Presentation.h,Presentation.s,Presentation.t,map_one,map_mul,map_inv,map_pow,
    FreeGroup.lift_apply_of,modelGenerators,Presentation.Generator.ofMaps]
  case ad a d => exact (A_D E σ hσ a.toAdd d.toAdd).eq
  case cd c d => exact (C_D E σ hσ c.toAdd d.toAdd).eq
  case bc b c => exact (B_C E σ hσ b.toAdd c.toAdd).eq
  case ca c a => exact C_A E σ hσ a.toAdd c.toAdd
  case bd b d =>
    change B E σ hσ b.toAdd*D E σ hσ d.toAdd=
      D E σ hσ d.toAdd*cHom E σ hσ 1*B E σ hσ b.toAdd
    rw [map_one,mul_one]
    exact (B_D E σ hσ _ _).eq
  case ba b a => exact B_A E σ hσ a.toAdd b.toAdd
  case ha k a =>
    change h E σ hσ k*A E σ hσ a.toAdd*(h E σ hσ k)⁻¹=_
    rw [FourTorus.h_A,mul_assoc,mul_inv_cancel,mul_one]
    rfl
  case hd k d =>
    change h E σ hσ k*D E σ hσ d.toAdd*(h E σ hσ k)⁻¹=_
    rw [FourTorus.h_D,mul_assoc,mul_inv_cancel,mul_one]
    rfl
  case hc k c =>
    change h E σ hσ k*C E σ hσ c.toAdd*(h E σ hσ k)⁻¹=_
    rw [FourTorus.h_C,mul_assoc,mul_inv_cancel,mul_one]
    rfl
  case hb k b =>
    change h E σ hσ k*B E σ hσ b.toAdd*(h E σ hσ k)⁻¹=_
    rw [FourTorus.h_B,mul_assoc,mul_inv_cancel,mul_one]
    rfl
  case ss => exact (FourBruhat.reflectionLaws E σ hσ).ss
  case tt => exact (FourBruhat.reflectionLaws E σ hσ).tt
  case st => exact st_four E σ hσ
  case sh k => exact FourCells.s_h E σ hσ k
  case th k => exact FourCells.t_h E σ hσ k
  case sd d => exact flip (FourBruhat.reflectionLaws E σ hσ).ss (s_B E σ hσ d.toAdd)
  case sc c => exact s_C E σ hσ c.toAdd
  case sb b => exact s_B E σ hσ b.toAdd
  case ta a => exact t_A E σ hσ a.toAdd
  case td d => exact t_D E σ hσ d.toAdd
  case tc c => exact flip (FourBruhat.reflectionLaws E σ hσ).tt (t_A E σ hσ c.toAdd)
  case sa a ha => exact FourBruhat.s_A E σ hσ a.toAdd (by simpa using ha)
  case tb b hb => exact FourBruhat.t_B E σ hσ b.toAdd (by simpa using hb)

theorem model_roots : (model_satisfies E σ hσ).roots=roots E σ hσ :=
  (parameters E σ hσ).roots_ofMaps (r := roots E σ hσ) (h := hHom E σ hσ)
    (s := s E σ hσ) (t := t E σ hσ) (model_satisfies E σ hσ)

theorem model_torus : (model_satisfies E σ hσ).torus=hHom E σ hσ :=
  (parameters E σ hσ).torus_ofMaps (r := roots E σ hσ) (h := hHom E σ hσ)
    (s := s E σ hσ) (t := t E σ hσ) (model_satisfies E σ hσ)

/-- Evaluation from the explicit presentation into the literal SU₄ carrier. -/
def evaluate : (parameters E σ hσ).Carrier →* SU E J :=
  (parameters E σ hσ).evaluate (model_satisfies E σ hσ)

/-- The unitary-four relations have no additional evaluation kernel. -/
theorem evaluate_injective : Function.Injective (evaluate E σ hσ) := by
  apply (parameters E σ hσ).evaluate_injective (model_satisfies E σ hσ)
  · rw [model_roots,model_torus]
    exact FourCells.borel_coordinates_injective E σ hσ
  · intro w hw
    apply (FourCells.weyl_mem_borel_iff E σ hσ w).mp
    exact hw
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourPresentation
