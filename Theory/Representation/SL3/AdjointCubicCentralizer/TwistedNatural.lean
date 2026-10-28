module
public import Theory.Representation.SL3.AdjointCubicCentralizer.FixedLevi
public import Theory.Representation.SL3.AdjointCubicCentralizer.BinarySimple

/-!
# A faithful binary adjoint extension with a natural cubic-fixed space

Place the determinant-twisted fixed space inside the full trace-zero carrier
and identify it with the natural plane under the literal lower Levi. Its
fixed subgroup is zero and its order over F₄ is sixteen. An inner diagonal
cubic still moves a vector of this same outer-cubic fixed space.

Together with BinarySimple and Faithful, this supplies a faithful irreducible
binary extension with the same SL₃ restriction as ordinary conjugation, but
with no binary equivalence between the extensions. It checks the model
against the fixed-space and surviving-movement data in 11.1.2. It does not
assert the full parabolic chief-factor profile from B.4.14, identify the
original chosen chief section, or refute the full ambient source theorem.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, B.4.14,
printed p.98, and 11.1.2, pp.763--764. The private inner-cubic calculation
is retained from the checked Scratch/LinearConstituents/Twist.lean.
-/

open Matrix
open scoped MatrixGroups
namespace Representation.SL3.AdjointCubicCentralizer
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (F : Type*) [Field F]

/-- The actual lower Levi inclusion into the projective group. -/
def projectiveLevi : SL(2,F) →* ProjGenLinGroup (Fin 3) F :=
  (ProjGenLinGroup.mk : (Mat3 F)ˣ →* _).comp (levi F)

/-- Fixed vectors in the full trace-zero carrier for the marked outer cubic. -/
def twistedCubicFixed (hc : ∀ u : Fˣ, u^3=1) (ω : Fˣ) : Submodule F (TraceZero F) where
  carrier := {v | projectiveTwistedAdjoint F hc (ProjGenLinGroup.mk (diagonalUnit F ω)) v = v}
  zero_mem' := map_zero _
  add_mem' {v w} hv hw := by
    change projectiveTwistedAdjoint F hc _ (v+w) = v+w
    rw [map_add,hv,hw]
  smul_mem' c v hv := by
    change projectiveTwistedAdjoint F hc _ (c • v) = c • v
    rw [map_smul,hv]

/-- Literal fixed-vector coordinates, preserving the full carrier inclusion. -/
def twistedCubicCoordinates (hc : ∀ u : Fˣ, u^3=1) (ω : Fˣ)
    (hω : (ω : F) ≠ 1) (hω2 : (ω : F)^2 ≠ 1) :
    twistedCubicFixed F hc ω ≃ₗ[F] (Fin 2 → F) :=
  (show twistedCubicFixed F hc ω ≃ₗ[F] twistedFixedSpace F ω from
    { toFun v := ⟨v.val.val,v.val.property,congrArg Subtype.val v.property⟩
      invFun v := ⟨⟨v.val,v.property.1⟩,Subtype.ext v.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }).trans (twistedFixedEquiv F ω hω hω2)

/-- The fixed-vector coordinates intertwine the actual projective Levi action. -/
theorem twistedCubicCoordinates_action (hc : ∀ u : Fˣ, u^3=1) (ω : Fˣ)
    (hω : (ω : F) ≠ 1) (hω2 : (ω : F)^2 ≠ 1)
    (g : SL(2,F)) (v : twistedCubicFixed F hc ω) :
    ∃ w : twistedCubicFixed F hc ω,
      w.val = projectiveTwistedAdjoint F hc (projectiveLevi F g) v.val ∧
      twistedCubicCoordinates F hc ω hω hω2 w =
        g.val *ᵥ twistedCubicCoordinates F hc ω hω hω2 v := by
  let e := twistedCubicCoordinates F hc ω hω hω2
  let w := e.symm (g.val *ᵥ e v)
  refine ⟨w,?_,e.apply_symm_apply _⟩
  have hv : column F (e v) = v.val.val :=
    congrArg (fun x : twistedCubicFixed F hc ω => x.val.val) (e.symm_apply_apply v)
  apply Subtype.ext
  change column F (g.val *ᵥ e v) = determinantTwist F (levi F g) v.val.val
  rw [←hv,column_levi_action]

/-- The only natural-plane vector fixed by the full SL₂ action is zero. -/
private theorem natural_fixed_zero (v : Fin 2 → F)
    (h : ∀ g : SL(2,F), g.val *ᵥ v = v) : v = 0 := by
  let a : SL(2,F) := ⟨!![1,1;0,1],by simp [Matrix.det_fin_two]⟩
  let b : SL(2,F) := ⟨!![1,0;1,1],by simp [Matrix.det_fin_two]⟩
  have h1 := congrFun (h a) 0
  have h0 := congrFun (h b) 1
  have hv1 : v 1 = 0 := by simpa [a,mulVec,dotProduct,Fin.sum_univ_two] using h1
  have hv0 : v 0 = 0 := by simpa [b,mulVec,dotProduct,Fin.sum_univ_two] using h0
  ext i
  fin_cases i <;> assumption

/-- The full Levi has no nonzero fixed vector on this cubic-fixed space. -/
theorem twistedCubicFixed_levi_fixed_eq_zero (hc : ∀ u : Fˣ, u^3=1) (ω : Fˣ)
    (hω : (ω : F) ≠ 1) (hω2 : (ω : F)^2 ≠ 1)
    (v : twistedCubicFixed F hc ω)
    (hv : ∀ g, projectiveTwistedAdjoint F hc (projectiveLevi F g) v.val = v.val) : v=0 := by
  let e := twistedCubicCoordinates F hc ω hω hω2
  apply e.injective
  rw [map_zero]
  apply natural_fixed_zero
  intro g
  obtain ⟨w,hw,he⟩ := twistedCubicCoordinates_action F hc ω hω hω2 g v
  have heq : w=v := Subtype.ext (hw.trans (hv g))
  simpa only [heq] using he.symm
/-- The determinant-one diagonal complementary to the outer diagonal cubic. -/
private def innerDiagonal (ω : Fˣ) : SL(2,F) :=
  ⟨!![(ω : F),0;0,(↑ω⁻¹ : F)],by simp [Matrix.det_fin_two]⟩

private theorem innerDiagonal_cube (hF : ∀ u : Fˣ, u^3 = 1) (ω : Fˣ) :
    innerDiagonal F ω ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow,Matrix.SpecialLinearGroup.coe_one]
  have he : (innerDiagonal F ω).val = Matrix.diagonal ![(ω : F),(↑ω⁻¹ : F)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [innerDiagonal]
  rw [he]
  rw [Matrix.diagonal_pow]
  have h1 : (ω : F)^3 = 1 := congrArg Units.val (hF ω)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1]

private theorem projective_innerDiagonal_order (hF : ∀ u : Fˣ, u^3 = 1)
    (ω : Fˣ) (hω : (ω : F) ≠ 1) :
    orderOf (Matrix.ProjGenLinGroup.mk (levi F (innerDiagonal F ω))) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [←map_pow,←map_pow,innerDiagonal_cube F hF,map_one,map_one]
  · intro h
    rw [Matrix.ProjGenLinGroup.mk_eq_one,Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
    obtain ⟨u,hu⟩ := h
    have h00 := congrArg (fun g : (Mat3 F)ˣ => g.val 0 0) hu
    have h11 := congrArg (fun g : (Mat3 F)ˣ => g.val 1 1) hu
    have hu1 : (u : F) = 1 := by
      simpa [Matrix.GeneralLinearGroup.coe_scalar,Matrix.scalar,levi,block] using h00
    have huω : (u : F) = (ω : F) := by
      simpa [Matrix.GeneralLinearGroup.coe_scalar,Matrix.scalar,levi,block,innerDiagonal] using h11
    exact hω (huω.symm.trans hu1)

/-- The same two torus directions used in the field-four extraspecial marking
also give nonzero cubic-fixed displacement in the determinant twist. -/
private theorem twisted_fixed_inner_displacement
    (hF : ∀ u : Fˣ, u^3 = 1) (ω : Fˣ) (hω : (ω : F) ≠ 1) :
    ∃ w : TraceZero F,
      projectiveTwistedAdjoint F hF (Matrix.ProjGenLinGroup.mk (diagonalUnit F ω)) w = w ∧
      projectiveTwistedAdjoint F hF (Matrix.ProjGenLinGroup.mk (levi F (innerDiagonal F ω))) w ≠ w := by
  let w : TraceZero F := ⟨column F ![1,0],(column_mem_twistedFixedSpace F ω ![1,0]).1⟩
  refine ⟨w,Subtype.ext (column_mem_twistedFixedSpace F ω ![1,0]).2,?_⟩
  intro h
  have hh := congrArg Subtype.val h
  change determinantTwist F (levi F (innerDiagonal F ω)) (column F ![1,0]) = column F ![1,0] at hh
  rw [column_levi_action] at hh
  have he := congrArg (fun M : Mat3 F => M 1 0) hh
  exact hω (by simpa [column,innerDiagonal,mulVec,dotProduct,Fin.sum_univ_two] using he)


variable [Finite F] [CharP F 2]
attribute [local instance] ZMod.algebra

/-- The binary extension has exactly the ordinary adjoint SL₃ restriction. -/
theorem binaryTwistedAdjoint_restriction (hF : Nat.card F = 4) :
    (binaryTwistedAdjoint F hF).comp Matrix.SpecialLinearGroup.toPGL =
      (restrictScalars (k := ZMod 2) (projectiveAdjoint F)).comp
        Matrix.SpecialLinearGroup.toPGL := by
  apply MonoidHom.ext
  intro g
  exact congrArg (fun f : Module.End F (TraceZero F) => f.restrictScalars (ZMod 2))
    (twistedAdjoint_specialLinear F g)

/-- Nevertheless there is no binary intertwining equivalence of the extensions. -/
theorem binaryTwistedAdjoint_not_equivalent (hF : Nat.card F = 4)
    (ω : Fˣ) (hω : (ω : F) ≠ 1) :
    ¬ Nonempty ((restrictScalars (k := ZMod 2) (projectiveAdjoint F)).Equiv
      (binaryTwistedAdjoint F hF)) := by
  rintro ⟨e⟩
  apply no_projective_intertwining_bijection F hF ω hω
  exact ⟨e.toLinearEquiv.toEquiv,fun g X => LinearMap.congr_fun (e.isIntertwining' g) X⟩

omit [CharP F 2] in
/-- The fixed space has order sixteen, exactly the natural quotient order
in the chosen-module comparison. -/
theorem twistedCubicFixed_card (hF : Nat.card F = 4) (ω : Fˣ)
    (hω : (ω : F) ≠ 1) :
    Nat.card (twistedCubicFixed F (units_cube_of_card_four F hF) ω) = 16 := by
  have hω2 := square_ne_one_of_cube F ω hω
    (congrArg Units.val (units_cube_of_card_four F hF ω))
  rw [Nat.card_congr (twistedCubicCoordinates F _ ω hω hω2).toEquiv,
    Nat.card_fun,Nat.card_fin,hF]
  decide

omit [CharP F 2] in
/-- A marked inner projective cubic moves a vector fixed by the outer cubic.
This reuses the original explicit torus calculation. -/
theorem twistedCubicFixed_inner_movement (hF : Nat.card F = 4) (ω : Fˣ)
    (hω : (ω : F) ≠ 1) :
    ∃ g : SL(2,F), orderOf (projectiveLevi F g) = 3 ∧
      ∃ v : twistedCubicFixed F (units_cube_of_card_four F hF) ω,
        projectiveTwistedAdjoint F (units_cube_of_card_four F hF)
          (projectiveLevi F g) v.val ≠ v.val := by
  obtain ⟨v,hfix,hmove⟩ := twisted_fixed_inner_displacement F
    (units_cube_of_card_four F hF) ω hω
  exact ⟨innerDiagonal F ω,projective_innerDiagonal_order F
    (units_cube_of_card_four F hF) ω hω,⟨v,hfix⟩,hmove⟩

end
end Representation.SL3.AdjointCubicCentralizer
