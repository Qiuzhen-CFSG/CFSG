module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.FourGroupGeometry
public import Theory.GroupTheory.MaximalTwoLocalElementary
public import Theory.ElementaryAbelian.Injective

/-!
# Zero and nonsingular form reduction for maximal two-locals

The radical of the native intrinsic alternating form is an actual elementary
subgroup of the matrix group. The whole ambient normalizer preserves it, and
its restricted form is zero. If the radical is trivial the original form is
nonsingular. Maximality among two-locals therefore gives a nontrivial elementary
normalizer witness in one of those two cases, with equality of full normalizers.

The final source trichotomy separates pure-2A groups from the two mixed cases.
In the mixed zero-form case it also places the group in the literal embedded
solvable residual of the marked 2B-involution's full centralizer. This is the
inner half required before the M22 image analysis, with no relative-normality,
full ambient Sylow or odd-index hypothesis added. The remaining native
container and order-256 geometry must still prove the four-local cover.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Section 2,
p.488, and the opening paragraphs of Sections 2.2 and 2.3, pp.489,492.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover
open LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB

variable (X : Subgroup Model) [IsElementaryAbelian 2 X]

/-- The ambient image of the radical of the actual intrinsic alternating form. -/
@[expose] def formRadical : Subgroup Model where
  carrier := {x | x ∈ X ∧ ∀ y ∈ X, outerValue x y = 0}
  one_mem' := ⟨X.one_mem, fun _ _ => outerValue_one_left _⟩
  mul_mem' := by
    intro x z hx hz
    refine ⟨X.mul_mem hx.1 hz.1, ?_⟩
    intro y hy
    have hm := congrArg (fun l => l (Additive.ofMul (⟨y, hy⟩ : X)))
      ((intrinsicElementaryForm X).map_add (Additive.ofMul (⟨x, hx.1⟩ : X))
        (Additive.ofMul (⟨z, hz.1⟩ : X)))
    change outerValue (x * z) y = outerValue x y + outerValue z y at hm
    simpa only [hx.2 y hy, hz.2 y hy, add_zero] using hm
  inv_mem' := by
    intro x hx
    have hsq : x * x = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hx.1
    simpa only [inv_eq_of_mul_eq_one_right hsq] using hx

theorem formRadical_le : formRadical X ≤ X := fun _ hx => hx.1

instance formRadical_elementary : IsElementaryAbelian 2 (formRadical X) :=
  IsElementaryAbelian.of_injective (inclusion (formRadical_le X)) (inclusion_injective _)

/-- Restriction to the intrinsic radical has zero form, including the identity row. -/
theorem formRadical_form_zero : intrinsicElementaryForm (formRadical X) = 0 := by
  ext x y
  exact x.toMul.property.2 y.toMul (formRadical_le X y.toMul.property)

private theorem formRadical_conj_mem (g : normalizer (X : Set Model))
    (x : Model) (hx : x ∈ formRadical X) : (MulAut.conj (g : Model)) x ∈ formRadical X := by
  refine ⟨((g.property) x).mp hx.1, ?_⟩
  intro y hy
  let f := X.normalizerMonoidHom g
  obtain ⟨v, hv⟩ := f.surjective (⟨y, hy⟩ : X)
  have he : (MulAut.conj (g : Model)) (v : Model) = y := congrArg Subtype.val hv
  rw [← he, outerValue_equiv]
  exact hx.2 v v.property

/-- The full ambient normalizer preserves the radical, without a Sylow hypothesis. -/
theorem normalizer_le_formRadical_normalizer :
    normalizer (X : Set Model) ≤ normalizer (formRadical X : Set Model) := by
  intro g hg x
  constructor
  · exact formRadical_conj_mem X ⟨g, hg⟩ x
  · intro hx
    change x ∈ formRadical X
    have hh := formRadical_conj_mem X (⟨g, hg⟩ : normalizer (X : Set Model))⁻¹ _ hx
    simpa only [Subgroup.coe_inv, MulAut.conj_apply, inv_inv, mul_assoc,
      inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

/-- Trivial radical is equivalent to nonsingularity for this symmetric form. -/
theorem formRadical_eq_bot_iff : formRadical X = ⊥ ↔
    (intrinsicElementaryForm X).Nondegenerate := by
  constructor
  · intro he
    have hleft : (intrinsicElementaryForm X).SeparatingLeft := by
      intro x hx
      have hm : (x.toMul : Model) ∈ formRadical X := ⟨x.toMul.property, fun y hy =>
        hx (Additive.ofMul ⟨y, hy⟩)⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mem_bot.mp (he ▸ hm)
    refine ⟨hleft, ?_⟩
    intro y hy
    apply hleft y
    intro x
    rw [(intrinsicElementaryForm_isSymm X).eq]
    exact hy x
  · intro h
    apply eq_bot_iff.mpr
    intro x hx
    have he := h.1 (Additive.ofMul (⟨x, hx.1⟩ : X)) (fun y => hx.2 y.toMul y.toMul.property)
    exact mem_bot.mpr (congrArg (fun w : Additive X => (w.toMul : Model)) he)

/-- The zero-form hypothesis places X in the literal embedded residual of
C(t), the actual inner half used in KW Section 2.2. -/
theorem zero_form_le_involution_residual (hform : intrinsicElementaryForm X = 0)
    (t : Model) (ht : t ∈ X) (ht1 : t ≠ 1) :
    X ≤ (solvableResidual (centralizer ({t} : Set Model))).map
      (centralizer ({t} : Set Model)).subtype := by
  intro y hy
  apply (outerValue_eq_zero_iff t y ht1).mp
  have he := congrArg (fun B : LinearMap.BilinForm (ZMod 2) (Additive X) =>
    B (Additive.ofMul ⟨t, ht⟩) (Additive.ofMul ⟨y, hy⟩)) hform
  exact he

/-- KW Section 2's initial reduction: every maximal two-local is the full
normalizer of a nontrivial elementary group with zero or nonsingular form. -/
theorem maximal_twoLocal_zero_or_nonsingular (M : Subgroup Model) (hM : IsMaximalTwoLocal M) :
    ∃ X : Subgroup Model, X ≠ ⊥ ∧ ∃ _hX : IsElementaryAbelian 2 X,
      M = normalizer (X : Set Model) ∧
      (intrinsicElementaryForm X = 0 ∨ (intrinsicElementaryForm X).Nondegenerate) := by
  obtain ⟨X, hXne, hX, hMX⟩ := exists_elementary_normalizer_of_isMaximalTwoLocal hM
  let := hX
  by_cases hrad : formRadical X = ⊥
  · exact ⟨X, hXne, hX, hMX, Or.inr ((formRadical_eq_bot_iff X).mp hrad)⟩
  · have hlocal : IsTwoLocal (normalizer (formRadical X : Set Model)) :=
      ⟨formRadical X, hrad, IsElementaryAbelian.isPGroup 2 _, rfl⟩
    have hle : M ≤ normalizer (formRadical X : Set Model) := by
      rw [hMX]
      exact normalizer_le_formRadical_normalizer X
    exact ⟨formRadical X, hrad, inferInstance, hM.eq_of_le hlocal hle,
      Or.inl (formRadical_form_zero X)⟩

/-- The three source branches, with the entire maximal two-local retained.
The mixed zero-form branch includes the literal full-centralizer residual
placement, and both mixed branches have an actual ambient second-class marker. -/
theorem maximal_twoLocal_source_cases (M : Subgroup Model) (hM : IsMaximalTwoLocal M) :
    ∃ X : Subgroup Model, X ≠ ⊥ ∧ ∃ _hX : IsElementaryAbelian 2 X,
      M = normalizer (X : Set Model) ∧
      (((∀ x ∈ X, x ≠ 1 → IsConj a x) ∧ intrinsicElementaryForm X = 0) ∨
        ∃ t ∈ X, orderOf t = 2 ∧ ¬ IsConj a t ∧
          IsConj ((a * b * a * b * b) ^ 5) t ∧
          ((intrinsicElementaryForm X = 0 ∧
            X ≤ (solvableResidual (centralizer ({t} : Set Model))).map
              (centralizer ({t} : Set Model)).subtype) ∨
            (intrinsicElementaryForm X).Nondegenerate)) := by
  obtain ⟨X, hXne, hX, hMX, hform⟩ := maximal_twoLocal_zero_or_nonsingular M hM
  let := hX
  refine ⟨X, hXne, hX, hMX, ?_⟩
  by_cases hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x
  · exact Or.inl ⟨hpure, pure_first_intrinsicForm_zero X hpure⟩
  · obtain ⟨t, ht, ht2, hnt, hsecond⟩ := nonpure_contains_second X hpure
    refine Or.inr ⟨t, ht, ht2, hnt, hsecond, ?_⟩
    rcases hform with hz | hns
    · refine Or.inl ⟨hz, zero_form_le_involution_residual X hz t ht ?_⟩
      intro he
      simp [he] at ht2
    · exact Or.inr hns

end Janko4.LocalStructure.ElementaryNormalizerCover
