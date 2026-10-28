module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CubicNormalizer
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CubicNormalizer

/-!
# The symmetric factor of a cubic centralizer

The centralizer of a full-support cubic in the plus-four orthogonal group
is C₃ × S₃. Its involutions lie in the S₃ factor, which is normalized by the
whole cubic normalizer S₃ × S₃. Consequently any order-six subgroup generated
by two involutions and centralizing the cubic is this same symmetric factor.
The centralizer is the product of the cubic and that factor.

The internal import intentionally shares the coordinate implementation of
`CubicNormalizer`. Only the coordinate-free conclusion is exported.

Source: Aschbacher–Smith, Lemma 13.5.15, printed p.920. The source's assertion
that the cubic centralizer is S₃ omits its central cubic factor. The normality
argument uses the unique S₃ factor, whereas the full centralizer has order18.
-/

open Subgroup
namespace BinaryFourPlus.CubicNormalizer

private instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd S3 C2).injective.decidableEq
private instance : Fintype Wreath :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd S3 C2).symm

private theorem factor_injective (side : Bool) : Function.Injective (factor side) := by
  have hh := (MonoidHom.noncommCoprod_injective
    (factor false) (factor true) factor_commute).mp full_injective
  cases side
  · exact hh.1
  · exact hh.2.1

private theorem factor_range_card (side : Bool) : Nat.card (factor side).range = 6 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (factor_injective side)).toEquiv]
  norm_num [S3, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem full_range_eq_normalizer (side : Bool) :
    full.range = normalizer (zpowers (rotation side) : Set Wreath) := by
  obtain ⟨⟨e⟩, _⟩ := models side
  apply eq_of_le_of_card_ge (full_normalizes side)
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective full_injective).toEquiv]

private theorem normalizer_le_factor_normalizer (side : Bool) :
    normalizer (zpowers (rotation side) : Set Wreath) ≤
      normalizer ((factor (!side)).range : Set Wreath) := by
  rw [← full_range_eq_normalizer side]
  have hc : (factor false).range ≤ centralizer ((factor true).range : Set Wreath) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact (factor_commute a b).eq.symm
  have hc' := le_centralizer_iff.mp hc
  change (MonoidHom.noncommCoprod (factor false) (factor true) factor_commute).range ≤ _
  rw [MonoidHom.noncommCoprod_range]
  cases side
  · exact sup_le (hc.trans (centralizer_le_normalizer _)) (factor true).range.le_normalizer
  · exact sup_le (factor false).range.le_normalizer
      (hc'.trans (centralizer_le_normalizer _))

private theorem involution_mem_factor (side : Bool) (w : Wreath)
    (hw : w ^ 2 = 1) (hc : w * rotation side = rotation side * w) :
    w ∈ (factor (!side)).range := by
  change ∃ p, factor (!side) p = w
  have hh : ∀ (side : Bool) (w : Wreath), w ^ 2 = 1 →
      w * rotation side = rotation side * w → ∃ p, factor (!side) p = w := by
    decide +kernel
  exact hh side w hw hc

private theorem rotationHom_range (side : Bool) :
    (rotationHom side).range = zpowers (rotation side) := by
  have hi : Function.Injective (rotationHom side) :=
    ((MonoidHom.noncommCoprod_injective _ _ _).mp (central_injective side)).1
  apply eq_of_le_of_card_ge
  · rintro _ ⟨i, rfl⟩
    exact npow_mem_zpowers (rotation side) i.toAdd.val
  · rw [Nat.card_zpowers, rotation_order,
      ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    norm_num [C3, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

private theorem cubic_disjoint_factor (side : Bool) :
    Disjoint (zpowers (rotation side)) (factor (!side)).range := by
  have hd : Disjoint (rotationHom side).range (factor (!side)).range :=
    ((MonoidHom.noncommCoprod_injective _ _ _).mp (central_injective side)).2.2
  rwa [rotationHom_range] at hd

private theorem centralizer_eq_cubic_sup_factor (side : Bool) :
    centralizer (zpowers (rotation side) : Set Wreath) =
      zpowers (rotation side) ⊔ (factor (!side)).range := by
  have hc : centralizer (zpowers (rotation side) : Set Wreath) =
      centralizer ({rotation side} : Set Wreath) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hc, ← central_range]
  change (MonoidHom.noncommCoprod (rotationHom side) (factor (!side)) _).range = _
  rw [MonoidHom.noncommCoprod_range, rotationHom_range]

/-- The order-six involution pair is the normal symmetric factor of the
marked cubic centralizer. The full centralizer also contains the cubic. -/
public theorem symmetric_factor_normalizer (A J : Subgroup Wreath)
    (hA : Nat.card A = 3) (s : Wreath) (hs : s ≠ 1)
    (hss : SingularDisplacements s) (hcentral : s ∈ centralizer (A : Set Wreath))
    (hJcentral : J ≤ centralizer (A : Set Wreath)) (hJcard : Nat.card J = 6)
    (hJgen : ∃ a b : Wreath, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ J = zpowers a ⊔ zpowers b) :
    normalizer (A : Set Wreath) ≤ normalizer (J : Set Wreath) ∧
      centralizer (A : Set Wreath) = A ⊔ J ∧ Disjoint A J ∧
      Nat.card (A ⊔ J : Subgroup Wreath) = 18 := by
  obtain ⟨side, rfl⟩ := cyclic_position A hA s hs hss hcentral
  obtain ⟨a, b, ha, hb, hJ⟩ := hJgen
  have hac : a ∈ centralizer (zpowers (rotation side) : Set Wreath) := by
    apply hJcentral
    rw [hJ]
    exact mem_sup_left (mem_zpowers a)
  have hbc : b ∈ centralizer (zpowers (rotation side) : Set Wreath) := by
    apply hJcentral
    rw [hJ]
    exact mem_sup_right (mem_zpowers b)
  have hle : J ≤ (factor (!side)).range := by
    rw [hJ]
    exact sup_le
      (zpowers_le.mpr (involution_mem_factor side a ha
        (mem_centralizer_iff.mp hac _ (mem_zpowers _)).symm))
      (zpowers_le.mpr (involution_mem_factor side b hb
        (mem_centralizer_iff.mp hbc _ (mem_zpowers _)).symm))
  have heq : J = (factor (!side)).range :=
    eq_of_le_of_card_ge hle (by rw [hJcard, factor_range_card])
  rw [heq]
  refine ⟨normalizer_le_factor_normalizer side, centralizer_eq_cubic_sup_factor side,
    cubic_disjoint_factor side, ?_⟩
  rw [← centralizer_eq_cubic_sup_factor]
  exact (normalizer_centralizer_card _ hA s hs hss hcentral).2

end BinaryFourPlus.CubicNormalizer
