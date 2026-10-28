module
public import Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Actors with generalized Fitting subgroup A₅ × A₅

The self-centralizing generalized Fitting subgroup has trivial center, so
conjugation embeds the whole group into Aut(A₅ × A₅). The marked wreath
product description gives order 28800, prime to seven. Thus the whole
actor cannot contain a seven-section.

This is the group comparison excluding G.11.2(7) for the original point
residual in Aschbacher--Smith 12.9.4, printed p.859. Its application uses
the actual projective orthogonal model equivalence.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating.FiveSquareFitting
open FiveSquareAutomorphisms

/-- The automorphism group of the two marked A₅ factors has order 28800. -/
theorem card_automorphism : Nat.card (MulAut Pair) = 28800 := by
  rw [Nat.card_congr wreathEquiv.symm.toEquiv,RegularWreathProduct.card]
  norm_num [FiveSquareAutomorphisms.Sym,Theory.GroupTheory.WreathTwoElementaryRank.C2,
    Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]

/-- An actor with generalized Fitting subgroup A₅×A₅ embeds into its
actual automorphism group: the self-centralizer is the trivial center. -/
def fittingConjugation {D : Type*} [Group D] [Finite D]
    (e : generalizedFitting D ≃* Pair) : D →* MulAut Pair :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem fittingConjugation_injective {D : Type*} [Group D] [Finite D]
    (e : generalizedFitting D ≃* Pair) : Function.Injective (fittingConjugation e) := by
  have hZ : center Pair = ⊥ := by
    rw [Subgroup.center_prod,alternatingGroup.center_eq_bot (by simp),bot_prod_bot]
  have hC : centralizer (generalizedFitting D : Set D) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxH := centralizer_generalizedFitting_le D hx
    have hz : e ⟨x,hxH⟩ ∈ center Pair := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z,rfl⟩ := e.surjective y
      rw [←map_mul,←map_mul]
      apply congrArg e
      exact Subtype.ext (mem_centralizer_iff.mp hx z z.property)
    rw [hZ,mem_bot] at hz
    have he := e.injective (hz.trans e.map_one.symm)
    exact congrArg Subtype.val he
  have ha : Function.Injective (MulAut.conjNormal : D →* MulAut (generalizedFitting D)) := by
    rw [←MonoidHom.ker_eq_bot_iff,MulAut.conjNormal_ker_eq_centralizer,hC]
  exact (MulAut.congr e).injective.comp ha

/-- In particular seven cannot divide the order of such a whole actor. -/
theorem seven_not_dvd {D : Type*} [Group D] [Finite D]
    (e : generalizedFitting D ≃* Pair) : ¬ 7 ∣ Nat.card D := by
  intro hd
  have hh := hd.trans (card_dvd_of_injective (fittingConjugation e) (fittingConjugation_injective e))
  rw [card_automorphism] at hh
  exact (by decide : ¬ 7 ∣ 28800) hh

end Theory.SpecificGroups.Alternating.FiveSquareFitting
