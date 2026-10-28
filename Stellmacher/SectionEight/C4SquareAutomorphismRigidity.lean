module

public import Stellmacher.LaterDefs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic

namespace Stellmacher.SectionEight

set_option synthInstance.maxSize 2048

private abbrev Square := Later.C4 × Later.C4

private def first : Square := (Multiplicative.ofAdd 1, 1)

private def second : Square := (1, Multiplicative.ofAdd 1)

private def evaluate (left right element : Square) : Square :=
  left ^ element.1.toAdd.val * right ^ element.2.toAdd.val

private theorem generators (element : Square) : evaluate first second element = element := by
  revert element
  decide

private theorem hom_evaluate (hom : Square →* Square) (element : Square) :
    hom element = evaluate (hom first) (hom second) element := by
  conv_lhs => rw [← generators element]
  simp only [evaluate, map_mul, map_pow]

private theorem aut_evaluate (action : MulAut Square) (element : Square) :
    action element = evaluate (action first) (action second) element :=
  hom_evaluate action.toMonoidHom element

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem swap_coordinates : ∀ left right swapLeft swapRight : Square,
    left ^ 2 = first ^ 2 → right ^ 2 = second ^ 2 →
    swapLeft ^ 2 = second ^ 2 → swapRight ^ 2 = first ^ 2 →
    evaluate left right swapLeft = evaluate swapLeft swapRight left →
    evaluate left right swapRight = evaluate swapLeft swapRight right →
    left.1 = right.2 ∧ left.2 = right.1 := by
  unfold evaluate first second
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem shear_coordinates : ∀ left right shearLeft shearRight : Square,
    left ^ 2 = first ^ 2 → right ^ 2 = second ^ 2 →
    shearLeft ^ 2 = first ^ 2 → shearRight ^ 2 = (first * second) ^ 2 →
    evaluate left right shearLeft = evaluate shearLeft shearRight left →
    evaluate left right shearRight = evaluate shearLeft shearRight right →
    left.2 = 1 := by
  unfold evaluate first second
  decide

private theorem scalar_coordinates : ∀ left right : Square,
    left ^ 2 = first ^ 2 → right ^ 2 = second ^ 2 →
    left.1 = right.2 → left.2 = right.1 → left.2 = 1 →
    (left = first ∧ right = second) ∨ (left = first⁻¹ ∧ right = second⁻¹) := by
  unfold first second
  decide

private def swap : MulAut Square where
  toFun element := (element.2, element.1)
  invFun element := (element.2, element.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def shear : MulAut Square where
  toFun element := (element.1 * element.2, element.2)
  invFun element := (element.1 * element.2⁻¹, element.2)
  left_inv element := by ext <;> simp
  right_inv element := by ext <;> simp
  map_mul' left right := by ext <;> simp [mul_comm, mul_left_comm]

private theorem concrete_rigidity (action : MulAut Square)
    (hfix : ∀ element : Square, element ^ 2 = 1 → action element = element)
    (hlifts : ∀ symmetry : MulAut Square, ∃ lift : MulAut Square,
      (∀ element : Square, element ^ 2 = 1 → lift element = symmetry element) ∧
      ∀ element : Square, action (lift element) = lift (action element)) :
    (∀ element : Square, action element = element) ∨
      (∀ element : Square, action element = element⁻¹) := by
  have hfirst : (first ^ 2) ^ 2 = 1 := by decide
  have hsecond : (second ^ 2) ^ 2 = 1 := by decide
  have hleft : (action first) ^ 2 = first ^ 2 := by
    rw [← map_pow, hfix _ hfirst]
  have hright : (action second) ^ 2 = second ^ 2 := by
    rw [← map_pow, hfix _ hsecond]
  obtain ⟨swapLift, hswap, hswapComm⟩ := hlifts swap
  have hswapLeft : (swapLift first) ^ 2 = second ^ 2 := by
    rw [← map_pow, hswap _ hfirst]
    rfl
  have hswapRight : (swapLift second) ^ 2 = first ^ 2 := by
    rw [← map_pow, hswap _ hsecond]
    rfl
  have hswapCoords := swap_coordinates (action first) (action second)
    (swapLift first) (swapLift second) hleft hright hswapLeft hswapRight
    ((aut_evaluate action _).symm.trans ((hswapComm first).trans (aut_evaluate swapLift _)))
    ((aut_evaluate action _).symm.trans ((hswapComm second).trans (aut_evaluate swapLift _)))
  obtain ⟨shearLift, hshear, hshearComm⟩ := hlifts shear
  have hshearLeft : (shearLift first) ^ 2 = first ^ 2 := by
    rw [← map_pow, hshear _ hfirst]
    decide
  have hshearRight : (shearLift second) ^ 2 = (first * second) ^ 2 := by
    rw [← map_pow, hshear _ hsecond]
    decide
  have hshearCoords := shear_coordinates (action first) (action second)
    (shearLift first) (shearLift second) hleft hright hshearLeft hshearRight
    ((aut_evaluate action _).symm.trans ((hshearComm first).trans (aut_evaluate shearLift _)))
    ((aut_evaluate action _).symm.trans ((hshearComm second).trans (aut_evaluate shearLift _)))
  obtain hscalar | hscalar := scalar_coordinates (action first) (action second)
    hleft hright hswapCoords.1 hswapCoords.2 hshearCoords
  · left
    intro element
    rw [aut_evaluate, hscalar.1, hscalar.2, generators]
  · right
    intro element
    rw [aut_evaluate, hscalar.1, hscalar.2]
    revert element
    decide

universe u

private theorem involution_membership {H : Type u} [CommGroup H]
    (model : H ≃* (Later.C4 × Later.C4)) (Z : Subgroup H)
    (hcard : Nat.card Z = 4) (hsquare : ∀ element : Z, (element : H) ^ 2 = 1)
    (element : H) : element ∈ Z ↔ element ^ 2 = 1 := by
  let embed : Z → {value : Later.C4 × Later.C4 // value ^ 2 = 1} :=
    fun value => ⟨model value, by rw [← map_pow, hsquare, map_one]⟩
  have hinj : Function.Injective embed := by
    intro left right heq
    apply Subtype.ext
    exact model.injective (congrArg Subtype.val heq)
  have hcount : Nat.card {value : Later.C4 × Later.C4 // value ^ 2 = 1} = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hsurj := ((Nat.bijective_iff_injective_and_card embed).mpr
    ⟨hinj, hcard.trans hcount.symm⟩).2
  constructor
  · exact fun hmem => hsquare ⟨element, hmem⟩
  · intro hpow
    obtain ⟨preimage, heq⟩ := hsurj
      ⟨model element, by rw [← map_pow, hpow, map_one]⟩
    have hval : (preimage : H) = element := model.injective (congrArg Subtype.val heq)
    exact hval ▸ preimage.property

private def restrictInvolutions {H : Type u} [CommGroup H] (Z : Subgroup H)
    (hfull : ∀ element : H, element ∈ Z ↔ element ^ 2 = 1)
    (symmetry : MulAut H) : MulAut Z where
  toFun element := ⟨symmetry element, (hfull _).mpr (by
    rw [← map_pow, (hfull _).mp element.property, map_one])⟩
  invFun element := ⟨symmetry.symm element, (hfull _).mpr (by
    rw [← map_pow, (hfull _).mp element.property, map_one])⟩
  left_inv element := Subtype.ext (symmetry.symm_apply_apply element)
  right_inv element := Subtype.ext (symmetry.apply_symm_apply element)
  map_mul' left right := Subtype.ext (map_mul symmetry (left : H) (right : H))

private theorem transport_lifts {H : Type u} [CommGroup H]
    (model : H ≃* (Later.C4 × Later.C4)) (Z : Subgroup H)
    (hfull : ∀ element : H, element ∈ Z ↔ element ^ 2 = 1)
    (action : MulAut H)
    (hlifts : ∀ symmetry : MulAut Z, ∃ lift : MulAut H,
      (∀ element : Z, lift (element : H) = (symmetry element : H)) ∧
      ∀ element : H, action (lift element) = lift (action element))
    (symmetry : MulAut (Later.C4 × Later.C4)) :
    ∃ lift : MulAut (Later.C4 × Later.C4),
      (∀ element : Later.C4 × Later.C4, element ^ 2 = 1 → lift element = symmetry element) ∧
      ∀ element : Later.C4 × Later.C4,
        (model.symm.trans (action.trans model)) (lift element) =
          lift ((model.symm.trans (action.trans model)) element) := by
  let originalSymmetry := model.trans (symmetry.trans model.symm)
  obtain ⟨lift, hagrees, hcommutes⟩ := hlifts (restrictInvolutions Z hfull originalSymmetry)
  refine ⟨model.symm.trans (lift.trans model), ?_, ?_⟩
  · intro element hsquare
    have hmem : model.symm element ∈ Z := (hfull _).mpr (by
      rw [← map_pow, hsquare, map_one])
    have heq := congrArg model (hagrees ⟨model.symm element, hmem⟩)
    simpa [restrictInvolutions, originalSymmetry] using heq
  · intro element
    simpa using congrArg model (hcommutes (model.symm element))

public theorem c4_square_automorphism_rigidity {H : Type u} [CommGroup H]
    (model : H ≃* (Later.C4 × Later.C4)) (Z : Subgroup H)
    (hcard : Nat.card Z = 4) (hsquare : ∀ z : Z, (z : H) ^ 2 = 1)
    (action : MulAut H) (hfix : ∀ z : Z, action (z : H) = z)
    (hlifts : ∀ symmetry : MulAut Z, ∃ lift : MulAut H,
      (∀ z : Z, lift (z : H) = (symmetry z : H)) ∧
      ∀ element : H, action (lift element) = lift (action element)) :
    (∀ element : H, action element = element) ∨
      (∀ element : H, action element = element⁻¹) := by
  have hfull := involution_membership model Z hcard hsquare
  let coordinateAction : MulAut Square := model.symm.trans (action.trans model)
  have hcoordinateFix : ∀ element : Square, element ^ 2 = 1 →
      coordinateAction element = element := by
    intro element hpow
    have hmem : model.symm element ∈ Z := (hfull _).mpr (by
      rw [← map_pow, hpow, map_one])
    simpa [coordinateAction] using congrArg model (hfix ⟨model.symm element, hmem⟩)
  obtain hidentity | hinversion := concrete_rigidity coordinateAction hcoordinateFix
    (transport_lifts model Z hfull action hlifts)
  · left
    intro element
    apply model.injective
    simpa [coordinateAction] using hidentity (model element)
  · right
    intro element
    apply model.injective
    simpa [coordinateAction] using hinversion (model element)

end Stellmacher.SectionEight

