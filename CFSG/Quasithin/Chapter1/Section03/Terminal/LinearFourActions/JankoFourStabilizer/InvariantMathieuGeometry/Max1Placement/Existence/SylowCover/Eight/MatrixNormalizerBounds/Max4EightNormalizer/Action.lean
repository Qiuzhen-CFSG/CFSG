module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4Transport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Action.Table

/-!
# All automorphisms of the literal max4 eight are realized in max4

The certified eight-word multiplication table identifies its elements by
indices 0 through 7. Indices 1, 2, 3 form a basis: all other elements are their
specified products. Every automorphism therefore gives an ordered basis, and
the checked `Action.Table` supplies a word in the two actual max4 generators
with the same action. Equality on the basis gives equality on the whole eight.

The tables use right conjugation. The normalizer homomorphism uses left
conjugation, so its surjectivity witness is the inverse of that word.
The full ambient centralizer bound is a separate obligation in the parent.

Source: the ATLAS J4G1-max4W1 words and Kleidman–Wilson (1988), pp.484–510,
with provenance retained in `Max4.NormalEight`. This is the concrete action
input to the Sylow-overgroup argument used in Aschbacher–Smith A.3.12.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear
open Janko4.LocalStructure.SymmetricLinear.NormalEight
attribute [local irreducible] modelGroup matrixA matrixB

/-- The ambient image of the normal eight is normalized by all of literal max4. -/
theorem max4_le_eight_normalizer : max4Subgroup ≤ normalizer (max4Eight : Set Model) := by
  let := normal_eight
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    eight.le_normalizer_map max4Subgroup.subtype

namespace Max4EightAction

private def wordElement : List Bool → max4Subgroup
  | [] => 1
  | b :: w => (if b then y else x) * wordElement w

private lemma wordElement_conj (w : List Bool) (i : Fin 8) :
    (wordElement w)⁻¹ * element i * wordElement w = element (wordAction w i) := by
  induction w generalizing i with
  | nil => simp [wordElement, wordAction]
  | cons b w ih =>
    cases b <;>
      simp only [wordElement, wordAction, Bool.false_eq_true, if_false, if_true,
        mul_inv_rev]
    · calc
        _ = (wordElement w)⁻¹ * (x⁻¹ * element i * x) * wordElement w := by group
        _ = _ := by rw [element_conj_x, ih]
    · calc
        _ = (wordElement w)⁻¹ * (y⁻¹ * element i * y) * wordElement w := by group
        _ = _ := by rw [element_conj_y, ih]

private lemma wordAction_mul (w : List Bool) (i j : Fin 8) :
    wordAction w (productIndex i j) = productIndex (wordAction w i) (wordAction w j) := by
  apply element_injective
  rw [← element_mul, ← wordElement_conj, ← wordElement_conj, ← wordElement_conj,
    ← element_mul]
  group

private lemma wordAction_zero (w : List Bool) : wordAction w 0 = 0 := by
  apply element_injective
  rw [← wordElement_conj, element_zero]
  simp

private lemma indexHom_ext (p q : Fin 8 → Fin 8)
    (hp : ∀ i j, p (productIndex i j) = productIndex (p i) (p j))
    (hq : ∀ i j, q (productIndex i j) = productIndex (q i) (q j))
    (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2) (h3 : p 3 = q 3) : p = q := by
  have h4 : p 4 = q 4 := (hp 1 3).trans ((congrArg₂ productIndex h1 h3).trans (hq 1 3).symm)
  have h5 : p 5 = q 5 := (hp 1 2).trans ((congrArg₂ productIndex h1 h2).trans (hq 1 2).symm)
  have h6 : p 6 = q 6 := (hp 2 3).trans ((congrArg₂ productIndex h2 h3).trans (hq 2 3).symm)
  have h7 : p 7 = q 7 := (hp 1 6).trans ((congrArg₂ productIndex h1 h6).trans (hq 1 6).symm)
  funext i
  fin_cases i <;> assumption

private def ambientElement (i : Fin 8) : max4Eight :=
  ⟨(element i : Model), mem_map_of_mem max4Subgroup.subtype (show element i ∈ eight from ⟨i, rfl⟩)⟩

private lemma ambientElement_injective : Function.Injective ambientElement := by
  intro i j h
  apply element_injective
  apply Subtype.ext
  exact congrArg (fun z : max4Eight => (z : Model)) h

private lemma ambientElement_surjective : Function.Surjective ambientElement := by
  rintro ⟨g, h⟩
  obtain ⟨a, ⟨i, rfl⟩, rfl⟩ := h
  exact ⟨i, rfl⟩

private lemma ambientElement_mul (i j : Fin 8) :
    ambientElement (productIndex i j) = ambientElement i * ambientElement j := by
  apply Subtype.ext
  exact congrArg (fun z : max4Subgroup => (z : Model)) (element_mul i j).symm

private lemma ambientElement_zero : ambientElement 0 = 1 := by
  apply Subtype.ext
  exact congrArg (fun z : max4Subgroup => (z : Model)) element_zero

private noncomputable def enumeration : Fin 8 ≃ max4Eight :=
  Equiv.ofBijective ambientElement ⟨ambientElement_injective, ambientElement_surjective⟩

private noncomputable def indexAction (f : MulAut max4Eight) (i : Fin 8) : Fin 8 :=
  enumeration.symm (f (ambientElement i))

private lemma ambientElement_indexAction (f : MulAut max4Eight) (i : Fin 8) :
    ambientElement (indexAction f i) = f (ambientElement i) :=
  enumeration.apply_symm_apply _

private lemma indexAction_injective (f : MulAut max4Eight) : Function.Injective (indexAction f) :=
  enumeration.symm.injective.comp (f.injective.comp ambientElement_injective)

private lemma indexAction_zero (f : MulAut max4Eight) : indexAction f 0 = 0 := by
  apply ambientElement_injective
  rw [ambientElement_indexAction, ambientElement_zero, map_one]

private lemma indexAction_mul (f : MulAut max4Eight) (i j : Fin 8) :
    indexAction f (productIndex i j) = productIndex (indexAction f i) (indexAction f j) := by
  apply ambientElement_injective
  simp only [ambientElement_indexAction, ambientElement_mul, map_mul]

private lemma indexAction_basis (f : MulAut max4Eight) :
    IsBasis (indexAction f 1) (indexAction f 2) (indexAction f 3) := by
  have hi := indexAction_injective f
  have h0 := indexAction_zero f
  have hm := indexAction_mul f 1 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h0]; exact fun h => (by decide : (1 : Fin 8) ≠ 0) (hi h)
  · rw [← h0]; exact fun h => (by decide : (2 : Fin 8) ≠ 0) (hi h)
  · exact fun h => (by decide : (2 : Fin 8) ≠ 1) (hi h)
  · rw [← h0]; exact fun h => (by decide : (3 : Fin 8) ≠ 0) (hi h)
  · exact fun h => (by decide : (3 : Fin 8) ≠ 1) (hi h)
  · exact fun h => (by decide : (3 : Fin 8) ≠ 2) (hi h)
  · rw [← hm]; exact fun h => (by decide : (3 : Fin 8) ≠ productIndex 1 2) (hi h)

private lemma exists_word_action (f : MulAut max4Eight) :
    ∃ w : List Bool, ∀ i, wordAction w i = indexAction f i := by
  let w := wordFor (indexAction f 1) (indexAction f 2) (indexAction f 3)
  obtain ⟨h1, h2, h3⟩ := wordFor_spec _ _ _ (indexAction_basis f)
  have he := indexHom_ext (wordAction w) (indexAction f) (wordAction_mul w)
    (indexAction_mul f) ((wordAction_zero w).trans (indexAction_zero f).symm) h1 h2 h3
  exact ⟨w, congrFun he⟩

/-- Every automorphism of the embedded eight is right conjugation by an actual max4 word. -/
theorem realizes_automorphism (f : MulAut max4Eight) :
    ∃ g : max4Subgroup, ∀ u : max4Eight, (f u : Model) = (g : Model)⁻¹ * (u : Model) * (g : Model) := by
  obtain ⟨w, hw⟩ := exists_word_action f
  refine ⟨wordElement w, ?_⟩
  intro u
  obtain ⟨i, rfl⟩ := ambientElement_surjective u
  have he := wordElement_conj w i
  rw [hw] at he
  exact (congrArg Subtype.val (ambientElement_indexAction f i)).symm.trans
    (congrArg Subtype.val he).symm

end Max4EightAction

/-- The normalizer action restricted to literal max4 is the full automorphism group. -/
theorem max4_eight_action_surjective : Function.Surjective (max4Eight.normalizerMonoidHom.comp
    (max4Subgroup.subgroupOf (normalizer (max4Eight : Set Model))).subtype) := by
  intro f
  obtain ⟨g, hg⟩ := Max4EightAction.realizes_automorphism f
  refine ⟨⟨⟨(g : Model)⁻¹, max4_le_eight_normalizer (max4Subgroup.inv_mem g.property)⟩,
    max4Subgroup.inv_mem g.property⟩, ?_⟩
  ext u
  change (g : Model)⁻¹ * (u : Model) * ((g : Model)⁻¹)⁻¹ = (f u : Model)
  rw [inv_inv, hg u]

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
