module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The field extension of PSL(3,4)

Over `GaloisField 2 2`, squaring is a nontrivial involutive field automorphism.
Entrywise application preserves determinant one and the scalar center, hence
induces an involution of PSL(3,4). Its action defines the actual semidirect
product `FieldExtension = PSL ⋊ C2`. The linear subgroup is identified with the
kernel of the split projection to `C2`.

The finite-field identity `x⁴ = x` proves involutivity. The existing determinant
kernel and scalar-center count gives the orders 20160 and 40320.

Source: Aschbacher, *Sporadic Groups*, §18 (especially 18.7–18.9); the extension
appearing in quasithin Lemma 5.2.18(1). The full projective semilinear group is a
distinct, larger group, not the definition used here.
-/

public section

namespace Matrix.PSL3Four
noncomputable section
/-- The field with four elements, shared with the coordinate plane. -/
abbrev F := GaloisField 2 2
/-- The common coordinate carrier for projective points and line covectors. -/
abbrev PG := Projectivization F (Fin 3 → F)
/-- The determinant-one matrix group in dimension three. -/
abbrev SL := SpecialLinearGroup (Fin 3) F
/-- The central quotient of the determinant-one matrix group. -/
abbrev PSL := ProjectiveSpecialLinearGroup (Fin 3) F
/-- The cyclic group of order two, in multiplicative notation. -/
abbrev C2 := Multiplicative (ZMod 2)

theorem card_F : Nat.card F = 4 := by
  simpa using GaloisField.card 2 2 (by decide)

theorem pow_four (x : F) : x ^ 4 = x := by
  let := Fintype.ofFinite F
  have hc : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, card_F]
  simpa [hc] using FiniteField.pow_card x

/-- The nontrivial field automorphism, given by squaring. -/
@[expose] def fieldFrobenius : F ≃+* F :=
  { frobenius F 2 with
    invFun := frobenius F 2
    left_inv := fun x => by
      change (x ^ 2) ^ 2 = x
      simpa only [← pow_mul] using pow_four x
    right_inv := fun x => by
      change (x ^ 2) ^ 2 = x
      simpa only [← pow_mul] using pow_four x }

@[simp] theorem fieldFrobenius_apply (x : F) : fieldFrobenius x = x ^ 2 := rfl

@[simp] theorem fieldFrobenius_involutive (x : F) :
    fieldFrobenius (fieldFrobenius x) = x := by
  simpa only [fieldFrobenius_apply, ← pow_mul] using pow_four x

theorem exists_fieldFrobenius_ne : ∃ x : F, fieldFrobenius x ≠ x := by
  classical
  by_contra h
  push Not at h
  let := Fintype.ofFinite F
  have hs : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro x _
    have hx : x * (x - 1) = 0 := by
      have hx := h x
      rw [fieldFrobenius_apply] at hx
      calc
        x * (x - 1) = x ^ 2 - x := by ring
        _ = 0 := sub_eq_zero.mpr hx
    simpa only [Finset.mem_insert, Finset.mem_singleton, sub_eq_zero] using
      (mul_eq_zero.mp hx)
  have hc := Finset.card_le_card hs
  have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, card_F]
  simp only [Finset.card_univ, hcard] at hc
  have hle : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
  omega

/-- Entrywise Frobenius on determinant-one matrices. -/
@[expose] def slFrobenius : MulAut SL :=
  { SpecialLinearGroup.map fieldFrobenius.toRingHom with
    invFun := SpecialLinearGroup.map fieldFrobenius.toRingHom
    left_inv := fun A => by ext i j; exact fieldFrobenius_involutive (A i j)
    right_inv := fun A => by ext i j; exact fieldFrobenius_involutive (A i j) }

@[simp] theorem slFrobenius_apply (A : SL) (i j : Fin 3) :
    slFrobenius A i j = (A i j) ^ 2 := rfl

@[simp] theorem slFrobenius_involutive (A : SL) :
    slFrobenius (slFrobenius A) = A := by
  ext i j
  exact fieldFrobenius_involutive (A i j)

/-- Entrywise Frobenius descended through the center of SL. -/
@[expose] def pslFrobenius : MulAut PSL :=
  QuotientGroup.congr _ _ slFrobenius (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.centerCongr slFrobenius ⟨y, hy⟩).property
    · intro hx
      exact ⟨slFrobenius.symm x,
        (Subgroup.centerCongr slFrobenius.symm ⟨x, hx⟩).property,
        slFrobenius.apply_symm_apply x⟩)

@[simp] theorem pslFrobenius_mk (A : SL) :
    pslFrobenius (A : PSL) = (slFrobenius A : PSL) := rfl

@[simp] theorem pslFrobenius_involutive (A : PSL) :
    pslFrobenius (pslFrobenius A) = A := by
  induction A using QuotientGroup.induction_on with
  | H A => simp

theorem pslFrobenius_sq : pslFrobenius ^ 2 = 1 := by
  ext A
  exact pslFrobenius_involutive A

/-- The homomorphism from `C2` specified by an element whose square is one. -/
@[expose] def involutionHom {G : Type*} [Group G] (a : G) (ha : a ^ 2 = 1) : C2 →* G where
  toFun t := a ^ t.toAdd.val
  map_one' := by simp
  map_mul' := by
    intro x y
    change ZMod 2 at x y
    change a ^ (x + y).val = a ^ x.val * a ^ y.val
    fin_cases x <;> fin_cases y
    · change a ^ 0 = a ^ 0 * a ^ 0
      simp
    · change a ^ 1 = a ^ 0 * a ^ 1
      simp
    · change a ^ 1 = a ^ 1 * a ^ 0
      simp
    · change a ^ 0 = a ^ 1 * a ^ 1
      simpa only [pow_zero, pow_one, ← pow_two] using ha.symm

@[simp] theorem involutionHom_generator {G : Type*} [Group G] (a : G) (ha : a ^ 2 = 1) :
    involutionHom a ha (Multiplicative.ofAdd (1 : ZMod 2)) = a := by
  change a ^ 1 = a
  exact pow_one a

/-- The action of the field automorphism group on PSL(3,4). -/
@[expose] def fieldAction : C2 →* MulAut PSL := involutionHom pslFrobenius pslFrobenius_sq

@[simp] theorem fieldAction_generator :
    fieldAction (Multiplicative.ofAdd (1 : ZMod 2)) = pslFrobenius :=
  involutionHom_generator _ _

/-- PSL(3,4) extended by its field automorphism, as an actual semidirect product. -/
abbrev FieldExtension := PSL ⋊[fieldAction] C2

/-- The canonical inclusion of the linear subgroup. -/
@[expose] def linearInclusion : PSL →* FieldExtension := SemidirectProduct.inl
/-- The split projection recording the field-automorphism component. -/
@[expose] def fieldProjection : FieldExtension →* C2 := SemidirectProduct.rightHom
/-- The canonical field-automorphism complement. -/
@[expose] def fieldInclusion : C2 →* FieldExtension := SemidirectProduct.inr

theorem linearInclusion_injective : Function.Injective linearInclusion :=
  SemidirectProduct.inl_injective

theorem fieldProjection_surjective : Function.Surjective fieldProjection :=
  SemidirectProduct.rightHom_surjective

theorem range_linearInclusion : linearInclusion.range = fieldProjection.ker :=
  SemidirectProduct.range_inl_eq_ker_rightHom

/-- The linear subgroup is precisely the kernel of the field projection. -/
@[expose] def linearEquivKernel : PSL ≃* fieldProjection.ker where
  toFun A := ⟨linearInclusion A, by rfl⟩
  invFun A := A.val.left
  left_inv A := rfl
  right_inv A := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact A.property.symm
  map_mul' A B := Subtype.ext (map_mul linearInclusion A B)

theorem card_PSL : Nat.card PSL = 20160 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  norm_num [card_F, Fin.prod_univ_succ] at h
  change Nat.card PSL * 3 * 3 = 181440 at h
  omega

instance : Finite FieldExtension :=
  Finite.of_equiv (PSL × C2) SemidirectProduct.equivProd.symm

@[simp] theorem fieldProjection_linearInclusion (A : PSL) :
    fieldProjection (linearInclusion A) = 1 := rfl

@[simp] theorem fieldProjection_fieldInclusion (t : C2) :
    fieldProjection (fieldInclusion t) = t := rfl

@[simp] theorem linearEquivKernel_apply (A : PSL) :
    (linearEquivKernel A).val = linearInclusion A := rfl

theorem linear_mul_field (g : FieldExtension) :
    linearInclusion g.left * fieldInclusion g.right = g :=
  SemidirectProduct.inl_left_mul_inr_right g

theorem field_conjugates_linear (t : C2) (A : PSL) :
    fieldInclusion t * linearInclusion A * (fieldInclusion t)⁻¹ =
      linearInclusion (fieldAction t A) := by
  simpa only [fieldInclusion, linearInclusion, map_inv] using
    (SemidirectProduct.inl_aut (φ := fieldAction) t A).symm

theorem card_C2 : Nat.card C2 = 2 := by
  exact Nat.card_zmod 2

theorem card_FieldExtension : Nat.card FieldExtension = 40320 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, card_PSL, card_C2]

end
end Matrix.PSL3Four
