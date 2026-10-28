module
public import Theory.SpecificGroups.PSL2.CartanPanelFixedPoints
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.LinearPanelRegularity

/-!
# Punctured-panel double transitivity for every even linear model

The upper triangular matrices act on the affine line by translations
and multiplication by squares. Every scalar is a square in a finite
field of characteristic two, so this action is doubly transitive.
The calculation descends to PSL₂ and conjugates to every natural point
stabilizer. In particular the field of order two is retained.

These concrete ordered-pair actions supply the original linear endpoint
application of Fong--Seitz I (2A)--(2B), printed pp.7--9, through the same
local-model and panel maps in the companion source module. No unknown
group identification, local-cover classification or perfectness is assumed.
-/

public noncomputable section
open Subgroup BenderSuzuki.Converse Projectivization
open scoped LinearAlgebra.Projectivization MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.LinearPanel
variable {F : Type*} [Field F]

private def affine (t : F) : P1 F := Projectivization.mk F ![t,1]
  (by intro h; simpa using congrFun h 1)

private theorem exists_affine {x : P1 F} (hx : x ≠ pInf F) : ∃ t, affine t = x := by
  induction x using Projectivization.ind with | h v hv =>
    have hv1 : v 1 ≠ 0 := by
      intro hz
      apply hx
      apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
      refine ⟨v 0, ?_⟩
      funext i
      fin_cases i <;> simp [hz]
    refine ⟨v 0 / v 1, (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨(v 1)⁻¹, ?_⟩⟩
    funext i
    fin_cases i <;> simp [div_eq_mul_inv,mul_comm,inv_mul_cancel₀ hv1]

private theorem uni_affine (a t : F) : uni a • affine t = affine (a+t) := by
  change Projectivization.mk F _ _ = _
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;> simp [smul_eq_mulVec,Matrix.mulVec,dotProduct,Fin.sum_univ_two,add_comm]

private theorem tor_affine (a : Fˣ) (t : F) :
    tor a • affine t = affine ((a:F)^2*t) := by
  change Projectivization.mk F _ _ = _
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  refine ⟨(a:F)⁻¹, ?_⟩
  funext i
  fin_cases i <;> simp [smul_eq_mulVec,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    pow_two,mul_assoc]

variable [Finite F] [CharP F 2]
/-- The actual even linear Borel is doubly transitive off its fixed point. -/
theorem borel_two_transitive_off :
    ∀ a b c d : P1 F, a ≠ pInf F → b ≠ pInf F → c ≠ pInf F → d ≠ pInf F →
      a ≠ b → c ≠ d → ∃ g ∈ Borel F, g • a = c ∧ g • b = d := by
  intro a b c d ha hb hc hd hab hcd
  obtain ⟨a,rfl⟩ := exists_affine ha
  obtain ⟨b,rfl⟩ := exists_affine hb
  obtain ⟨c,rfl⟩ := exists_affine hc
  obtain ⟨d,rfl⟩ := exists_affine hd
  have hab' : b-a ≠ 0 := sub_ne_zero.mpr (fun he => hab (congrArg affine he.symm))
  have hcd' : d-c ≠ 0 := sub_ne_zero.mpr (fun he => hcd (congrArg affine he.symm))
  obtain ⟨z,hz⟩ := isSquare_of_charTwo' ((d-c)/(b-a))
  have hz0 : z ≠ 0 := by
    intro he
    simp [he,div_eq_zero_iff,hab',hcd'] at hz
  have hzs : z^2 = (d-c)/(b-a) := by simpa only [pow_two] using hz.symm
  let g := uni (c-z^2*a) * tor (Units.mk0 z hz0)
  refine ⟨g, ?_, ?_, ?_⟩
  · apply (Borel F).mul_mem
    · exact (Unip_le_Borel (F := F)) ((mem_Unip_iff _).mpr ⟨_,rfl⟩)
    · exact (show Torus F ≤ Borel F from inf_le_left)
        (by rw [Torus_eq_range]; exact ⟨_,rfl⟩)
  · change (uni _ * tor _) • affine a = _
    rw [mul_smul,tor_affine,uni_affine]
    congr 1
    simp
  · change (uni _ * tor _) • affine b = _
    rw [mul_smul,tor_affine,uni_affine]
    apply congrArg affine
    change c-z^2*a+z^2*b=d
    rw [hzs]
    field_simp
    ring

open PanelKernel
/-- The same ordered-pair property for the actual projective action. -/
theorem projective_borel_two_transitive_off :
    TwoTransitiveOff (PBorel F) (pInf F) := by
  intro a b c d ha hb hc hd hab hcd
  obtain ⟨g,hg,hga,hgb⟩ := borel_two_transitive_off a b c d ha hb hc hd hab hcd
  refine ⟨pi F g, ?_, ?_, ?_⟩
  · rw [PBorel_eq_map]
    exact mem_map_of_mem (pi F) hg
  · simpa only [pi_smul] using hga
  · simpa only [pi_smul] using hgb

/-- Every natural point stabilizer has the same punctured ordered-pair action. -/
theorem point_two_transitive_off (o : P1 F) :
    TwoTransitiveOff (MulAction.stabilizer PSL(2,F) o) o := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(2,F) (pInf F) o
  apply TwoTransitiveOff.pushforward (MulAut.conj g).toMonoidHom (MulAction.toPerm g)
    (B := PBorel F) (o := pInf F) ?_ ?_ hg projective_borel_two_transitive_off
  · change (MulAction.stabilizer PSL(2,F) (pInf F)).map (MulAut.conj g).toMonoidHom ≤ _
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hg]
  · intro a x
    change g • (a • x) = (g*a*g⁻¹) • (g • x)
    simp only [mul_smul,inv_smul_smul]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.LinearPanel
