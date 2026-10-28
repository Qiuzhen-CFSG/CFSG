module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.ModelEightCells
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourRootGeneration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group

/-!
# FourGeneration

The first two diagonal entries are converted between the native character
(a,ab) and the presentation parameter (a,b). The character kernel is the
positive subgroup, so the generated Borel is the whole literal flag overlap.
Existing elementary matrix generation now gives all of SU₄ and removes the
generation guard from its eight-cell theorem, including q=2. Source:
Steinberg, Lectures on Chevalley Groups, Theorems 4 and 33.
-/
@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourCells
open UnitaryFourFlag UnitaryFourSylow UnitaryFourGeneration SmallCompletion FourPositive FourWeyl
variable (E : Type*) [Field E] [Finite E] [CharP E 2]
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
local notation "J" => form E σ hσ
local notation "K" => FixedField E σ

/-- Convert the native character (a,ab) to the presentation's (a,b). -/
def parameterOfCharacter (a : Eˣ) (k : Kˣ) : torusParameters E σ :=
  ⟨(a,Units.map (FixedField E σ).subtype.toMonoidHom k*a⁻¹),by
    change σ ((a:E)*↑(Units.map (FixedField E σ).subtype.toMonoidHom k*a⁻¹))=
      (a:E)*↑(Units.map (FixedField E σ).subtype.toMonoidHom k*a⁻¹)
    simp only [Units.val_mul,Units.val_inv_eq_inv_val,Units.coe_map]
    change σ ((a:E)*(((k:K):E)*(a:E)⁻¹))=(a:E)*(((k:K):E)*(a:E)⁻¹)
    have he : (a:E)*(((k:K):E)*(a:E)⁻¹)=((k:K):E) := by field_simp
    rw [he]
    exact (k:K).property⟩

omit [CharP E 2] in
theorem h_mem_borel (p : torusParameters E σ) : h E σ hσ p∈borelSU E J := by
  apply (mem_borel_iff_triangular E σ hσ _).mpr
  rw [h_val]
  exact Matrix.blockTriangular_diagonal _

def characterLift (a : Eˣ) (k : Kˣ) : borelSU E J :=
  ⟨h E σ hσ (parameterOfCharacter E σ a k),h_mem_borel E σ hσ _⟩

omit [CharP E 2] in
theorem character_lift (a : Eˣ) (k : Kˣ) :
    torusCharacter E σ hσ (characterLift E σ hσ a k)=(a,k) := by
  apply Prod.ext
  · apply Units.ext
    rw [torusCharacter_fst_val]
    change (h E σ hσ (parameterOfCharacter E σ a k)).val.val 0 0=(a:E)
    rw [h_val]
    rfl
  · apply Units.ext; apply Subtype.ext
    rw [torusCharacter_snd_val]
    change (h E σ hσ (parameterOfCharacter E σ a k)).val.val 0 0*
      (h E σ hσ (parameterOfCharacter E σ a k)).val.val 1 1=((k:K):E)
    rw [h_val]
    simp [Matrix4.H,parameterOfCharacter]
    field_simp

/-- The generated root-and-torus Borel is the full literal flag overlap. -/
theorem borel_eq : (roots E σ hσ).borel (hHom E σ hσ)=borelSU E J := by
  apply le_antisymm
  · apply sup_le
    · rw [generated_eq_upper]
      exact upper_le_borel E σ hσ
    · rintro x ⟨p,rfl⟩
      apply (mem_borel_iff_triangular E σ hσ _).mpr
      change (h E σ hσ p).val.val |>.IsUpperTriangular
      rw [h_val]
      exact Matrix.blockTriangular_diagonal _
  · intro g hg
    let c := torusCharacter E σ hσ ⟨g,hg⟩
    let d := characterLift E σ hσ c.1 c.2
    have hd : d.val∈(roots E σ hσ).borel (hHom E σ hσ) := by
      exact (roots E σ hσ).torus_mem_borel (hHom E σ hσ) _
    have hu : g*d.val⁻¹∈upper E σ hσ := by
      have hc : (⟨g,hg⟩ : borelSU E J)*d⁻¹∈(torusCharacter E σ hσ).ker := by
        change torusCharacter E σ hσ ((⟨g,hg⟩ : borelSU E J)*d⁻¹)=1
        rw [map_mul,map_inv,character_lift]
        exact mul_inv_cancel c
      rw [torusCharacter_ker] at hc
      exact hc
    have hU : upper E σ hσ≤(roots E σ hσ).borel (hHom E σ hσ) := by
      rw [←generated_eq_upper]
      exact le_sup_left
    have he : g=(g*d.val⁻¹)*d.val := by group
    rw [he]
    exact ((roots E σ hσ).borel (hHom E σ hσ)).mul_mem (hU hu) hd

/-- These exact presentation generators generate every special-unitary matrix. -/
theorem fullGenerated_eq_top :
    ReflectionLaws.fullGenerated (roots E σ hσ) (hHom E σ hσ) (s E σ hσ) (t E σ hσ)=⊤ := by
  let H := ReflectionLaws.fullGenerated (roots E σ hσ) (hHom E σ hσ) (s E σ hσ) (t E σ hσ)
  have hB : (roots E σ hσ).borel (hHom E σ hσ)≤H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  apply FourRootGeneration.eq_top E σ hσ H
  · intro a
    have ha := hB ((roots E σ hσ).A_mem_borel (hHom E σ hσ) (Multiplicative.ofAdd (σ a)))
    change A E σ hσ (σ a)∈H at ha
    simpa only [A,hσ a] using ha
  · intro b
    exact hB ((roots E σ hσ).B_mem_borel (hHom E σ hσ) (Multiplicative.ofAdd b))
  · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · intro g hg
    exact hB ((borel_eq E σ hσ).symm ▸ FourDiagonal.mem_borel E σ hσ g hg)

/-- Unconditional eight-cell coverage of the full SU₄ model, including q=2. -/
theorem all_eight_cells (x : SU E J) : ∃ w : WeylWord,
    InCell (borelSU E J) (w.eval (s E σ hσ) (t E σ hσ)) x := by
  rw [←borel_eq]
  apply eight_cells E σ hσ
  rw [fullGenerated_eq_top]
  trivial
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourCells
