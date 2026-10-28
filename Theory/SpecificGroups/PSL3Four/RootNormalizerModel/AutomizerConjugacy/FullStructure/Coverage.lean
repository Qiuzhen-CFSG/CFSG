module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure.NormalForms

/-!
# Coverage of root automorphisms by shift–semilinear normal forms

Every automorphism of the literal group UT₃(F₄) is a central additive shift
followed by diagonal scalings, the graph involution, and Frobenius.

Squares detect the union of the two root axes modulo the center. After a
possible graph correction, commutation with a noncentral first-root element
forces preservation of that axis; its nontrivial commutator with a second-root
element forces preservation of the other axis. The commutator pairing then
identifies the two additive coordinate maps, after scaling, with one field
automorphism. The degree-two Galois bound identifies it as identity or
Frobenius. The already proved coordinate kernel supplies the central shift.

Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.3, 46.14.
The unconditional coverage theorem supplies the premise of
`FullStructure.torus_sylow_of_coverage` and
`FullStructure.normalizer_innerTorus_le_of_coverage`.
-/

@[expose] public section

open scoped commutatorElement
namespace Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
noncomputable section
open SylowModel

private def X (x : F) : Root := ⟨x, 0, 0⟩
private def Y (y : F) : Root := ⟨0, y, 0⟩
private def Z (c : F) : Root := ⟨0, 0, c⟩

private theorem square_coordinates (q : Root) : q * q = Z (q.x * q.y) := by
  apply U.ext <;> simp [Z, CharTwo.add_self_eq_zero]

private theorem central_image (a : MulAut Root) (c : F) :
    (a (Z c)).x = 0 ∧ (a (Z c)).y = 0 := by
  exact (mem_center_U _).mp
    (Subgroup.centerCongr a ⟨Z c, (mem_center_U _).mpr ⟨rfl, rfl⟩⟩).property

private theorem central_image_ne (a : MulAut Root) {c : F} (hc : c ≠ 0) :
    (a (Z c)).c ≠ 0 := by
  intro h
  have he : a (Z c) = 1 := U.ext (central_image a c).1 (central_image a c).2 h
  have hz : Z c = 1 := a.injective (he.trans (map_one a).symm)
  exact hc (congrArg U.c hz)

private theorem square_image (a : MulAut Root) (q : Root) (h : q * q = 1) :
    (a q).x * (a q).y = 0 := by
  have he : a q * a q = 1 := by rw [← map_mul, h, map_one]
  rw [square_coordinates] at he
  exact congrArg U.c he

private theorem commutator_image (a : MulAut Root) (x y : F) :
    (a (Z (x * y))).c = (a (X x)).x * (a (Y y)).y -
      (a (Y y)).x * (a (X x)).y := by
  have he := map_commutatorElement a (X x) (Y y)
  rw [commutator_coordinates, commutator_coordinates] at he
  simpa [X, Y, Z] using congrArg U.c he

private theorem commute_image (a : MulAut Root) (q r : Root) (h : q * r = r * q) :
    (a q).x * (a r).y = (a r).x * (a q).y := by
  apply (commute_iff _ _).mp
  rw [← map_mul, ← map_mul, h]

private theorem axes_of_first_nonzero (a : MulAut Root) (h : (a (X 1)).x ≠ 0) :
    (∀ x, (a (X x)).y = 0) ∧ (∀ y, (a (Y y)).x = 0) ∧
      (a (Y 1)).y ≠ 0 := by
  have hX (x : F) : X x * X x = 1 := by
    rw [square_coordinates]
    simp [X, Z]
    rfl
  have hy : (a (X 1)).y = 0 :=
    (mul_eq_zero.mp (square_image a _ (hX 1))).resolve_left h
  have hyall (x : F) : (a (X x)).y = 0 := by
    have he := commute_image a (X 1) (X x)
      ((commute_iff _ _).mpr (by simp [X]))
    rw [hy, mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left h
  have hv : (a (Y 1)).y ≠ 0 := by
    have he := commutator_image a 1 1
    simp only [one_mul, hy, mul_zero, sub_zero] at he
    intro hz
    rw [hz, mul_zero] at he
    exact central_image_ne a one_ne_zero he
  have hx : (a (Y 1)).x = 0 := by
    have he : Y 1 * Y 1 = 1 := by
      rw [square_coordinates]
      simp [Y, Z]
      rfl
    exact (mul_eq_zero.mp (square_image a _ he)).resolve_right hv
  refine ⟨hyall, ?_, hv⟩
  intro y
  have he := commute_image a (Y y) (Y 1)
    ((commute_iff _ _).mpr (by simp [Y]))
  rw [hx, zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_right hv

private def firstMap (a : MulAut Root) : F →+ F where
  toFun x := (a (X x)).x
  map_zero' := by change (a 1).x = 0; rw [map_one]; rfl
  map_add' x y := by
    have he : X (x + y) = X x * X y := by apply U.ext <;> simp [X]
    simp only [he, map_mul, mul_x]

private def secondMap (a : MulAut Root) : F →+ F where
  toFun y := (a (Y y)).y
  map_zero' := by change (a 1).y = 0; rw [map_one]; rfl
  map_add' x y := by
    have he : Y (x + y) = Y x * Y y := by apply U.ext <;> simp [Y]
    simp only [he, map_mul, mul_y]

private theorem action_coordinates (a : MulAut Root)
    (hX : ∀ x, (a (X x)).y = 0) (hY : ∀ y, (a (Y y)).x = 0) (q : Root) :
    (a q).x = firstMap a q.x ∧ (a q).y = secondMap a q.y := by
  have hq : q = X q.x * Y q.y * Z (q.c - q.x * q.y) := by
    apply U.ext <;> simp [X, Y, Z]
  have he := congrArg a hq
  rw [map_mul, map_mul] at he
  constructor
  · change (a q).x = (a (X q.x)).x
    have hh := congrArg U.x he
    simpa only [mul_x, (central_image a _).1, hY, add_zero] using hh
  · change (a q).y = (a (Y q.y)).y
    have hh := congrArg U.y he
    simpa only [mul_y, (central_image a _).2, hX, zero_add, add_zero] using hh

-- The cardinality argument is the same one used for coefficient automorphisms
-- in PSL3Four.OuterPlane.FieldOccurrence, with only the field imports needed here.
private theorem field_equiv_cases (σ : F ≃+* F) :
    σ = RingEquiv.refl F ∨ σ = fieldFrobenius := by
  classical
  let j : (F ≃+* F) → (F ≃ₐ[ZMod 2] F) := fun τ =>
    AlgEquiv.ofRingEquiv (f := τ) (fun z =>
      congrArg (fun f : ZMod 2 →+* F => f z)
        (Subsingleton.elim (τ.toRingHom.comp (algebraMap (ZMod 2) F))
          (algebraMap (ZMod 2) F)))
  have hj : Function.Injective j := fun τ υ h => RingEquiv.ext fun x =>
    congrArg (fun f : F ≃ₐ[ZMod 2] F => f x) h
  let : Finite (F ≃+* F) := Finite.of_injective j hj
  let : Fintype (F ≃+* F) := Fintype.ofFinite _
  have hc : Fintype.card (F ≃+* F) ≤ 2 := by
    have h := Nat.card_le_card_of_injective j hj
    rw [IsGalois.card_aut_eq_finrank, GaloisField.finrank 2 (by decide),
      Nat.card_eq_fintype_card] at h
    exact h
  have hn : fieldFrobenius ≠ RingEquiv.refl F := by
    intro he
    obtain ⟨x, hx⟩ := exists_fieldFrobenius_ne
    exact hx (congrArg (fun τ : F ≃+* F => τ x) he)
  by_contra! hs
  have hh := (Finset.card_le_univ
    ({RingEquiv.refl F, fieldFrobenius, σ} : Finset (F ≃+* F))).trans hc
  simp [Ne.symm hs.1, Ne.symm hs.2, Ne.symm hn] at hh

private theorem scalar_field_form (u v : F →+ F) (w : F → F)
    (hu : u 1 ≠ 0) (hv : v 1 ≠ 0)
    (hw : ∀ x y, w (x * y) = u x * v y) :
    ∃ (d : Fˣ × Fˣ) (f : Bool), ∀ x : F,
      u x = (d.1 : F) * fieldChoice f x ∧
      v x = (d.2 : F) * fieldChoice f x := by
  have hrel (x : F) : u x * v 1 = u 1 * v x := by
    rw [← hw x 1, ← hw 1 x, mul_one, one_mul]
  have hprod (x y : F) : u (x * y) * v 1 = u x * v y := by
    rw [← hw (x * y) 1, mul_one, hw]
  have hmul (x y : F) : u (x * y) * u 1 = u x * u y := by
    apply mul_right_cancel₀ hv
    calc
      (u (x * y) * u 1) * v 1 = u 1 * (u (x * y) * v 1) := by ring
      _ = u 1 * (u x * v y) := by rw [hprod]
      _ = u x * (u 1 * v y) := by ring
      _ = u x * (u y * v 1) := by rw [← hrel]
      _ = (u x * u y) * v 1 := by ring
  let σ : F →+* F :=
    { toFun := fun x => u x / u 1
      map_zero' := by simp
      map_one' := by simp [hu]
      map_add' := fun x y => by simp only [map_add, add_div]
      map_mul' := fun x y => by
        change u (x * y) / u 1 = (u x / u 1) * (u y / u 1)
        field_simp
        exact hmul x y }
  let e : F ≃+* F := RingEquiv.ofBijective σ
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have he (x : F) : e x = u x / u 1 := rfl
  obtain ⟨f, hf⟩ : ∃ f : Bool, e = fieldChoice f := by
    rcases field_equiv_cases e with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  refine ⟨(Units.mk0 (u 1) hu, Units.mk0 (v 1) hv), f, fun x => ?_⟩
  have huform : u x = u 1 * e x := by rw [he]; field_simp
  have hvform : v x = v 1 * e x := by
    apply mul_left_cancel₀ hu
    rw [← hrel, huform]
    ring
  simpa only [Units.val_mk0, hf] using And.intro huform hvform

private theorem oriented_coordinate_action (a : MulAut Root) (h : (a (X 1)).x ≠ 0) :
    ∃ (d : Fˣ × Fˣ) (f : Bool), ∀ q : Root,
      (a q).x = (d.1 : F) * fieldChoice f q.x ∧
      (a q).y = (d.2 : F) * fieldChoice f q.y := by
  obtain ⟨hX, hY, hv⟩ := axes_of_first_nonzero a h
  have hw (x y : F) : (a (Z (x * y))).c = firstMap a x * secondMap a y := by
    change (a (Z (x * y))).c = (a (X x)).x * (a (Y y)).y
    simpa only [hX, mul_zero, sub_zero] using commutator_image a x y
  obtain ⟨d, f, hf⟩ := scalar_field_form (firstMap a) (secondMap a)
    (fun c => (a (Z c)).c) h hv hw
  refine ⟨d, f, fun q => ?_⟩
  exact ⟨(action_coordinates a hX hY q).1.trans (hf q.x).1,
    (action_coordinates a hX hY q).2.trans (hf q.y).2⟩

/-- Every automorphism induces a diagonal–graph–field action on the two
simple-root coordinates. The central coordinate is unrestricted here. -/
theorem exists_standardPart_coordinates (a : MulAut Root) :
    ∃ (d : Fˣ × Fˣ) (g f : Bool), ∀ q : Root,
      (a q).x = (standardPart d g f q).x ∧
      (a q).y = (standardPart d g f q).y := by
  by_cases hx : (a (X 1)).x = 0
  · have hy : (a (X 1)).y ≠ 0 := by
      intro hy
      have hc : a (X 1) ∈ Subgroup.center Root := (mem_center_U _).mpr ⟨hx, hy⟩
      have hi := (Subgroup.centerCongr a.symm ⟨a (X 1), hc⟩).property
      change a.symm (a (X 1)) ∈ Subgroup.center Root at hi
      rw [a.symm_apply_apply] at hi
      exact one_ne_zero ((mem_center_U _).mp hi).1
    have hb : ((graph * a) (X 1)).x ≠ 0 := hy
    obtain ⟨d, f, hd⟩ := oriented_coordinate_action (graph * a) hb
    refine ⟨(d.2, d.1), true, f, fun q => ?_⟩
    have hh := hd q
    change (a q).y = (d.1 : F) * fieldChoice f q.x ∧
      (a q).x = (d.2 : F) * fieldChoice f q.y at hh
    simpa only [standardPart_x, standardPart_y, Bool.true_eq, ↓reduceIte] using hh.symm
  · obtain ⟨d, f, hd⟩ := oriented_coordinate_action a hx
    refine ⟨d, false, f, fun q => ?_⟩
    simpa only [standardPart_x, standardPart_y, Bool.false_eq_true, ↓reduceIte] using hd q

/-- Every automorphism of the literal UT₃(F₄) carrier is a central additive
shift followed by diagonal scalings, graph, and Frobenius. -/
theorem normalForm_surjective : Function.Surjective normalForm :=
  normalForm_surjective_of_coordinate_action exists_standardPart_coordinates

end
end Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
