module
public import Theory.SpecificGroups.Janko1.Model.Presentation
public import Theory.GroupTheory.CosetWordCertificateBoolean
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# The cyclic subgroup used to bound the J₁ presentation

The third of the five defining ATLAS relators bounds `⟨ab⟩` by seven.
The coset certificate uses the redundant generator `c = ab`; its remaining
relators are inverses and cyclic rotations of the original words.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J1G1-P1,
inspected 8 October 2026. All equations here hold in the abstract presentation.
-/

@[expose] public section
namespace Janko1.PresentationBound
open Subgroup.CosetWordCertificate

def generator : Nat → AtlasPresentation
  | 0 => presentationGenerator false
  | 1 => presentationGenerator true
  | _ => presentationGenerator false * presentationGenerator true

def cyclic : Subgroup AtlasPresentation := Subgroup.zpowers (generator 2)

theorem relator_eval (i : Fin 5) :
    atlasWord (presentationGenerator false) (presentationGenerator true) i = 1 := by
  have he : FreeGroup.lift presentationGenerator =
      PresentedGroup.mk (Set.range atlasRelator) := by
    apply FreeGroup.ext_hom
    intro b
    rfl
  have h : FreeGroup.lift presentationGenerator (atlasRelator i) = 1 := by
    rw [he]
    exact atlasPresentation_relator i
  fin_cases i <;> simpa [atlasRelator, atlasWord, map_mul, map_pow, map_inv, FreeGroup.lift_apply_of] using h

theorem cyclic_bound : Finite cyclic ∧ Nat.card cyclic ≤ 7 := by
  have hp : generator 2 ^ 7 = 1 := relator_eval 2
  have hx : IsOfFinOrder (generator 2) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨7, by decide, hp⟩
  refine ⟨hx.finite_zpowers.to_subtype, ?_⟩
  change Nat.card (Subgroup.zpowers (generator 2)) ≤ 7
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by decide) hp

def variant (w : Word Nat) (inv : Bool) (offset : Nat) : Word Nat :=
  (if inv then FreeGroup.invRev w else w).rotate offset

theorem eval_variant (w : Word Nat) (hw : eval generator w = 1)
    (inv : Bool) (offset : Nat) : eval generator (variant w inv offset) = 1 := by
  have h : eval generator (if inv then FreeGroup.invRev w else w) = 1 := by
    cases inv <;> simp [hw, eval_invRev]
  simpa [eval, FreeGroup.lift_mk, variant, List.map_rotate] using
    List.prod_rotate_eq_one_of_prod_eq_one (by simpa [eval, FreeGroup.lift_mk] using h) offset

end Janko1.PresentationBound
