module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass
public import Stellmacher.SL2DerivedCard
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The order-three actor at n = 1

The C.1.17 definition uses PSL₂(2^n)' for every positive n. For n=1 its
actor has order three and its natural module has order four. These facts
follow from the actual matrix models: field transport and the canonical
SL₂-to-PSL₂ map identify PSL₂(F) with SL₂(ZMod 2), whose derived subgroup
has order three. No general pushing-up result from Stellmacher is used.

Source: Aschbacher–Smith C.1.17, combined manuscript (1 March 2004), p.126.
-/

public section

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles

open Theory.GroupTheory
open scoped MatrixGroups

variable {B H : Type*} [Group B] [Group H] [Finite H] (e : B →* H)
    {F : Type} [Field F] [CharP F 2]

/-- In the two-element field the source actor is the actual derived
order-three subgroup; the full projective group would have order six. -/
theorem NaturalModel.actor_card_of_field_card_two [Finite F]
    (m : NaturalModel e F) (hF : Nat.card F = 2) :
    Nat.card (generalizedFitting (LocalStar e)) = 3 := by
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq
    (by simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let g : PSL(2,F) ≃* SL(2,ZMod 2) :=
    Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm.trans (Atlas.fieldEquivSL 2 f)
  exact (Nat.card_congr m.actorIso.toEquiv).trans
    (Stellmacher.isSL2Two_commutator_card ⟨g⟩)

/-- The natural module for the order-three actor has four elements. -/
theorem NaturalModel.module_card_of_field_card_two
    (m : NaturalModel e F) (hF : Nat.card F = 2) :
    Nat.card (MovedModule e) = 4 := by
  rw [m.module_card, hF]
  norm_num

end CFSG.Quasithin.ChapterC.GlaubermanNiles
