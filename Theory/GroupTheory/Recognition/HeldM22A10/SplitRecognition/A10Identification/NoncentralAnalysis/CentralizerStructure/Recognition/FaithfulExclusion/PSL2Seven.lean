module

public import GorensteinWalter.PGammaL2
public import GorensteinWalter.PGL2NonsplitTorus
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Order eight in faithful proper extensions of PSL₂(7)

A finite group with a proper normal subgroup isomorphic to PSL₂(7) and
trivial centralizer of that subgroup contains an element of order eight.
Conjugation embeds the group into Aut(PSL₂(7)). The semilinear automorphism
theorem and triviality of prime-field automorphisms identify this group with
PGL₂(7), of order 336. Properness of the subgroup of order 168 forces the
embedding to be surjective. A generator of a nonsplit torus of order eight
then gives the required element.

This is the model obstruction used after the faithful-action argument in
D. Held, "A Characterization of some multiply transitive permutation groups,
I", Illinois J. Math. 13 (1969), 224--240, DOI 10.1215/ijm/1256053756,
Lemma 4.2, p.235. The centralizer hypothesis is essential to this argument.
-/

noncomputable section

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
namespace FaithfulExclusion

open GorensteinWalter

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem seven_odd_prime_power : IsOddPrimePower (Nat.card (ZMod 7)) := by
  refine ⟨7, 1, by decide, by decide, by decide, ?_⟩
  norm_num

private theorem seven_card_gt_three : 3 < Nat.card (ZMod 7) := by norm_num

private def pgl2SevenEquivAut :
    PGL2 (ZMod 7) ≃* MulAut (PSL2 (ZMod 7)) := by
  apply MulEquiv.ofBijective
    (pgl2InnerAutPSL2 (ZMod 7) seven_odd_prime_power seven_card_gt_three)
  refine ⟨pgl2InnerAutPSL2_injective _ _ _, ?_⟩
  intro a
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective (ZMod 7)
    (p := 7) (f := 1) (by norm_num) seven_odd_prime_power seven_card_gt_three a
  have hxleft : SemidirectProduct.inl x.left = x := by
    apply SemidirectProduct.ext
    · rfl
    · exact Subsingleton.elim _ _
  refine ⟨x.left, ?_⟩
  rw [← pGammaL2ToMulAutPSL2_inl, hxleft]
  exact hx

private theorem pgl2Seven_has_order_eight :
    ∃ x : PGL2 (ZMod 7), orderOf x = 8 := by
  obtain ⟨U, _, hcyc, hcard, _⟩ := pgl2_nonsplit_torus_reflection_data
    (F := ZMod 7) (p := 7) (f := 1) (by norm_num)
  have : Finite (PGL2 (ZMod 7)) := Finite.of_surjective
    Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
  refine ⟨x, ?_⟩
  rw [Subgroup.orderOf_coe, hx, hcard]
  norm_num

universe u

/-- A faithful proper extension of the actual PSL₂(7) model contains an
element of order eight. -/
public theorem exists_order_eight_of_proper_faithful_psl2Seven
    {B : Type u} [Group B] [Finite B]
    (N : Subgroup B) [N.Normal]
    (eN : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))
    (hproper : N ≠ ⊤)
    (hcentralizer : Subgroup.centralizer (N : Set B) = ⊥) :
    ∃ x : B, orderOf x = 8 := by
  have hconj : Function.Injective (MulAut.conjNormal (H := N)) :=
    MulAut.conjNormal_injective_of_centralizer_eq_bot N hcentralizer
  let f : B →* PGL2 (ZMod 7) := pgl2SevenEquivAut.symm.toMonoidHom.comp
    ((MulAut.congr eN).toMonoidHom.comp (MulAut.conjNormal (H := N)))
  have hf : Function.Injective f := pgl2SevenEquivAut.symm.injective.comp
    ((MulAut.congr eN).injective.comp hconj)
  have : Finite (PGL2 (ZMod 7)) := Finite.of_surjective
    Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hN : Nat.card N = 168 := by
    rw [Nat.card_congr eN.toEquiv, psl2_card_formula _ seven_odd_prime_power]
    norm_num
  have hPGL : Nat.card (PGL2 (ZMod 7)) = 336 := by
    rw [pgl2_card_formula]
    norm_num
  have hi : 1 < N.index := Subgroup.one_lt_index_of_ne_top hproper
  have hmul := N.index_mul_card
  rw [hN] at hmul
  have hsurj : Function.Surjective f :=
    (hf.bijective_of_nat_card_le (by rw [hPGL]; omega)).surjective
  obtain ⟨g, hg⟩ := pgl2Seven_has_order_eight
  obtain ⟨x, hx⟩ := hsurj g
  refine ⟨x, ?_⟩
  rw [← orderOf_injective f hf, hx, hg]

end FaithfulExclusion
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
