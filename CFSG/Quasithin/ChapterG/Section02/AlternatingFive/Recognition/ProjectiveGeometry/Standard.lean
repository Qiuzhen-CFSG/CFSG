module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.SourceInput
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.Representation.SL2FourNaturalOrbits.Model

/-!
# The marked natural plane over the concrete field of order four

The standard field point is the first coordinate line. Its literal root
subgroup is the upper unipotent Sylow subgroup. Common fixed vectors have
second coordinate zero, giving a coordinate equivalence between fixed vectors
in s natural copies and F₄^s. This includes s = 0 and gives order 2^(2s).
The parent projective-geometry constructor marks the original U* by this root.

Source: Aschbacher–Smith, G.1.1 and G.1.5(1–2), printed pp.327–328,
and the natural upper layer in G.2.4(6), printed p.334.
-/

@[expose] public section

open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry

/-- The explicit quadratic field F₂[a], with a² = a + 1. -/
abbrev F4 := Representation.SL2FourNatural.F

theorem field_card : Nat.card F4 = 4 := by
  rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]

/-- The first coordinate line in the actual natural plane. -/
def standardPoint : ProjectivePoint F4 :=
  ⟨F4 ∙ (![1, 0] : Fin 2 → F4), finrank_span_singleton (by
    intro h
    have := congrFun h 0
    simp at this)⟩

theorem mem_standardPoint (v : Fin 2 → F4) : v ∈ standardPoint.val ↔ v 1 = 0 := by
  change v ∈ F4 ∙ (![1, 0] : Fin 2 → F4) ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro hv
    refine ⟨v 0, ?_⟩
    funext i
    fin_cases i <;> simp [hv]

theorem root_standardPoint : RootGroup F4 standardPoint.val =
    Matrix.SpecialLinearGroup.upperUnipotent F4 := by
  ext x
  rw [Matrix.SpecialLinearGroup.mem_upperUnipotent]
  constructor
  · intro hx
    have he := hx.2 (![1, 0]) ((mem_standardPoint _).mpr (by simp))
    change x.val *ᵥ (![1, 0] : Fin 2 → F4) = _ at he
    have h00 : x.val 0 0 = 1 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 0
    have h10 : x.val 1 0 = 0 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 1
    have h11 : x.val 1 1 = 1 := by
      simpa only [det_fin_two, h00, h10, mul_zero, sub_zero, one_mul] using x.property
    refine ⟨x.val 0 1, ?_⟩
    apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.transvection_coe, h00, h10, h11]
  · rintro ⟨a, rfl⟩
    constructor
    · intro v
      apply (mem_standardPoint _).mpr
      change ((Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
        zero_ne_one a).val *ᵥ v) 1 - v 1 = 0
      simp [Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · intro v hv
      have hv := (mem_standardPoint v).mp hv
      change (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
        zero_ne_one a).val *ᵥ v = v
      funext i
      fin_cases i <;> simp [Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv]

private theorem upper_eq_transvection (a : F4) : Representation.SL2FourNatural.upper a =
    Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one a := by
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Representation.SL2FourNatural.upper, Matrix.SpecialLinearGroup.transvection_coe]

theorem root_fixed_iff (v : Fin 2 → F4) :
    (∀ a ∈ RootGroup F4 standardPoint.val, Matrix.mulVec a.val v = v) ↔ v 1 = 0 := by
  rw [← Representation.SL2FourNatural.upper_fixed_iff v]
  constructor
  · intro h a
    exact h _ (by rw [root_standardPoint, upper_eq_transvection]
                  exact (Matrix.SpecialLinearGroup.mem_upperUnipotent F4 _).mpr ⟨a, rfl⟩)
  · intro h a ha
    rw [root_standardPoint] at ha
    obtain ⟨b, rfl⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F4 a).mp ha
    rw [← upper_eq_transvection]
    exact h b

/-- The full root-fixed vector set in s natural copies has order 2^(2s). -/
theorem fixed_copies_card (s : ℕ) :
    Nat.card {v : Fin s → Fin 2 → F4 //
      ∀ a ∈ RootGroup F4 standardPoint.val, ∀ j, Matrix.mulVec a.val (v j) = v j} =
        2 ^ (2 * s) := by
  let e : {v : Fin s → Fin 2 → F4 //
      ∀ a ∈ RootGroup F4 standardPoint.val, ∀ j, Matrix.mulVec a.val (v j) = v j} ≃
      (Fin s → F4) := {
    toFun := fun v j => v.val j 0
    invFun := fun f => ⟨fun j => ![f j, 0], fun a ha j =>
      (root_fixed_iff _).mpr (by simp) a ha⟩
    left_inv := by
      intro v
      apply Subtype.ext
      funext j i
      have hv := (root_fixed_iff (v.val j)).mp (fun a ha => v.property a ha j)
      fin_cases i <;> simp [hv]
    right_inv := fun f => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin, field_card]
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
