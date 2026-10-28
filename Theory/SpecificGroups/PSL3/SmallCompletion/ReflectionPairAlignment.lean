module

public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelSemilinearExtension
public import Theory.SpecificGroups.PSL3.SmallCompletion.Weyl

/-!
# Simultaneous alignment of the two torus-twisted reflections

A single diagonal GL₃ conjugation removes both twists over the field of four
elements. At the SL₃ level the two remaining factors are literal cubic scalar
matrices; the existing projective torus kernel identifies them explicitly.
The same actor preserves both local endpoints and their whole Borel.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem diagonal_reflection_pair (d e : Fˣ × Fˣ) (i : Bool) :
    linearConjSL F (diagonalGL ![(e.2/e.1)*(d.2/d.1),d.2/d.1,1])
      (torusSL F (if i then e else d) * reflectionSL F i) =
      torusSL F (if i then (e.2,e.2) else (d.1,d.1)) * reflectionSL F i := by
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL]
  apply Units.ext
  simp only [Units.val_mul,SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.coe_mul,←Units.inv_eq_val_inv]
  simp only [diagonalGL,Units.val_inv_eq_inv_val]
  cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [torusSL_val,reflectionSL,Matrix.diagonal_mul,Matrix.mul_diagonal,
      mul_assoc,mul_left_comm,mul_comm,div_eq_mul_inv]
  all_goals field_simp

/-- One explicit diagonal actor sends both torus twists to the same standard
reflection pair, with every scalar factor discharged in the actual quotient. -/
theorem exists_diagonal_reflection_pair_alignment (hF : Nat.card F=4)
    (d e : Fˣ × Fˣ) :
    ∃ a : MulAut PSL(3,F),
      a (torusMap F d * reflection F false)=reflection F false ∧
      a (torusMap F e * reflection F true)=reflection F true ∧
      (pointParabolic F).map a.toMonoidHom=pointParabolic F ∧
      (lineParabolic F).map a.toMonoidHom=lineParabolic F ∧
      (borel F).map a.toMonoidHom=borel F := by
  let a := rootSemilinearActor F (e.2/e.1) (d.2/d.1) (RingEquiv.refl F)
  have hunit (u : Fˣ) : u^3=1 := by
    let := Fintype.ofFinite Fˣ
    have hh : u ^ Fintype.card Fˣ=1 := pow_card_eq_one
    simpa only [←Nat.card_eq_fintype_card,Nat.card_units,hF] using hh
  have hact (i : Bool) :
      a (torusMap F (if i then e else d) * reflection F i)=reflection F i := by
    change linearConj F (diagonalGL ![(e.2/e.1)*(d.2/d.1),d.2/d.1,1])
      (fieldAction F (RingEquiv.refl F)
        (projection F (torusSL F (if i then e else d) * reflectionSL F i))) = _
    rw [show fieldAction F (RingEquiv.refl F)=1 from map_one _]
    change linearConj F (diagonalGL ![(e.2/e.1)*(d.2/d.1),d.2/d.1,1])
      (QuotientGroup.mk (torusSL F (if i then e else d) * reflectionSL F i)) = _
    rw [linearConj_mk,diagonal_reflection_pair]
    change projection F (torusSL F (if i then (e.2,e.2) else (d.1,d.1)) *
      reflectionSL F i) = _
    rw [map_mul]
    change torusMap F (if i then (e.2,e.2) else (d.1,d.1)) * reflection F i = _
    have hs : torusMap F (if i then (e.2,e.2) else (d.1,d.1))=1 := by
      apply (BorelQuotient.torusMap_eq_one_iff F _).mpr
      cases i <;> exact ⟨rfl,hunit _⟩
    rw [hs,one_mul]
  have ha := rootSemilinearActor_endpoints F (e.2/e.1) (d.2/d.1) (RingEquiv.refl F)
  refine ⟨a,hact false,hact true,?_,?_,ha.2.2⟩
  · rw [pointParabolic_eq_sup,Subgroup.map_sup,ha.1,ha.2.2]
  · rw [lineParabolic_eq_sup,Subgroup.map_sup,ha.2.1,ha.2.2]

end Matrix.PSL3.SmallCompletion
