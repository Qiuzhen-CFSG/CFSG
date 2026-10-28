module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.ActionImage.Candidates
public import Theory.GroupTheory.PGroup.FrattiniProfile

/-!
# Color stabilizers for the actual candidate Frattini actions

A coloring of a concrete Frattini quotient bounds the normalizer action
when every automorphism of the candidate preserves it. The comparison
below embeds the actual action image into the color stabilizer; it does
not replace that image by an unrelated finite group. Intrinsic fiber
profiles provide one way to prove color preservation.

This is a certificate interface for the J₄ step of Aschbacher–Smith 1.3.4,
printed p.511/PDF p.528. Constructing the quotient comparisons and bounding
the finite stabilizers are separate mathematical obligations.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

namespace ActionImageCandidates

attribute [local irreducible] candidate

/-- Automorphisms preserving every color class, with no assumed order bound. -/
def colorStabilizer {V : Type*} [Group V] (color : V → ℕ) : Subgroup (MulAut V) where
  carrier := {a | ∀ v, color (a v) = color v}
  one_mem' _ := rfl
  mul_mem' ha hb v := (ha _).trans (hb v)
  inv_mem' {a} ha v := by
    have h := ha (a⁻¹ v)
    simpa only [MulAut.apply_inv_self] using h.symm

/-- An actual quotient comparison and an automorphism-invariant coloring
embed the original normalizer action image into its finite color stabilizer. -/
theorem frattiniAction_card_dvd_colorStabilizer (i : Fin 193)
    {V : Type*} [Group V] [Finite V]
    (e : (candidate i ⧸ frattini (candidate i)) ≃* V) (color : V → ℕ)
    (hcolor : ∀ (f : MulAut (candidate i)) v,
      color (MulAut.congr e (quotientAut (frattini (candidate i)) f) v) = color v) :
    Nat.card (fixedTwoFrattiniAction (candidate i)).range ∣
      Nat.card (colorStabilizer color) := by
  let action := fixedTwoFrattiniAction (candidate i)
  let inclusion : action.range →* colorStabilizer color :=
    ((MulAut.congr e).toMonoidHom.comp action.range.subtype).codRestrict
      (colorStabilizer color) (by
        rintro ⟨a, g, rfl⟩
        exact hcolor ((candidate i).normalizerMonoidHom g))
  apply card_dvd_of_injective inclusion
  intro a b h
  apply Subtype.ext
  apply (MulAut.congr e).injective
  exact congrArg Subtype.val h

/-- The order-centralizer fiber profile is preserved in any genuine coordinates
on the candidate Frattini quotient. -/
theorem color_invariant_of_orderCentralizerProfile (i : Fin 193)
    {V : Type*} [Group V]
    (e : (candidate i ⧸ frattini (candidate i)) ≃* V) (color : V → ℕ)
    (hcolor : ∀ x y : V,
      fiberProfile (fun g => e (QuotientGroup.mk' (frattini (candidate i)) g))
        (fun g => (orderOf g, Nat.card (centralizer ({g} : Set (candidate i))))) x =
      fiberProfile (fun g => e (QuotientGroup.mk' (frattini (candidate i)) g))
        (fun g => (orderOf g, Nat.card (centralizer ({g} : Set (candidate i))))) y →
      color x = color y) :
    ∀ (f : MulAut (candidate i)) v,
      color (MulAut.congr e (quotientAut (frattini (candidate i)) f) v) = color v := by
  intro f v
  apply hcolor
  apply fiberProfile_map _ _ f.toEquiv
    (MulAut.congr e (quotientAut (frattini (candidate i)) f)).toEquiv
  · intro g
    change e (QuotientGroup.mk' (frattini (candidate i)) (f g)) =
      e (quotientAut (frattini (candidate i)) f
        (e.symm (e (QuotientGroup.mk' (frattini (candidate i)) g))))
    rw [e.symm_apply_apply, quotientAut_apply_mk]
  · intro g
    exact @order_centralizer_label_mulAut (candidate i) inferInstance f g

end ActionImageCandidates

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
