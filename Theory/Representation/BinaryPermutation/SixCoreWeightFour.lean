module
public import Theory.Representation.BinaryPermutation.SixCoreSmallImage
public import Theory.Representation.BinaryPermutation.SixCoreOrbits

/-!
# Actors moving the six-letter augmentation core only in weight four

An even involution with no weight-two displacement is the identity. Hence
sign embeds any elementary actor whose nonzero displacements all have
weight four into a group of order two. A nontrivial such actor cannot fix
a hyperplane: the established hyperplane-fixer theorem makes it a
transposition, which has a weight-two displacement.

The finite checks use only pairs of the six coordinates, not a subgroup
catalogue. The source application is the mutual-normalization step in
Aschbacher–Smith 13.4.16, printed p.913, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.SixCoreWeightFour
abbrev S := Equiv.Perm (Fin 6)
abbrev W := core (Fin 6)
abbrev rho := coreRepresentation (Fin 6)
private def pair (i j : Fin 6) : W :=
  ⟨Pi.single i 1 + Pi.single j 1, by simp [mem_core, Finset.sum_add_distrib, Pi.single_apply, CharTwo.add_self_eq_zero]⟩
private theorem even_test : ∀ a : S, a ^ 2 = 1 → Equiv.Perm.sign a = 1 →
    (∀ i j : Fin 6, wordWeight (rho a (pair i j) - pair i j).val ≠ 2) → a = 1 := by
  decide +kernel

theorem even_eq_one (a : S) (ha : a ^ 2 = 1) (heven : Equiv.Perm.sign a = 1)
    (hw : ∀ v : W, rho a v ≠ v → wordWeight (rho a v - v).val = 4) : a = 1 := by
  apply even_test a ha heven
  intro i j ht
  by_cases he : rho a (pair i j) = pair i j
  · rw [he,sub_self] at ht
    have hz : wordWeight (0 : W).val = 0 := by decide
    omega
  · have h := hw (pair i j) he
    omega

theorem card_le_two (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hw : ∀ a ∈ A, ∀ v : W, rho a v ≠ v → wordWeight (rho a v - v).val = 4) :
    Nat.card A ≤ 2 := by
  let f := Equiv.Perm.sign.comp A.subtype
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp (by
    apply bot_unique
    intro a ha
    apply Subtype.ext
    exact even_eq_one a.val (elemPow_eq_one_of_isElementaryAbelian a.val a.property) ha
      (hw a.val a.property))
  exact (Nat.card_le_card_of_injective f hf).trans (by rw [Nat.card_eq_fintype_card]; decide)

private theorem swap_test : ∀ i j : Fin 6, i ≠ j → ∃ k : Fin 6,
    wordWeight (rho (Equiv.swap i j) (pair i k) - pair i k).val = 2 := by
  decide +kernel

theorem fixedCodim_two_le (A : Subgroup S) (hne : A ≠ ⊥)
    (hw : ∀ a ∈ A, ∀ v : W, rho a v ≠ v → wordWeight (rho a v - v).val = 4) :
    2 ≤ fixedCodim rho A := by
  by_contra! hn
  change fixedCodim (coreRepresentation (Fin 6)) A < 2 at hn
  obtain ⟨t,ht,hswap,_⟩ := SixCoreSmallImage.small_image_eq_zpowers A hne (by omega)
  obtain ⟨i,j,hij,rfl⟩ := hswap
  obtain ⟨k,hk⟩ := swap_test i j hij
  have hne : rho (Equiv.swap i j) (pair i k) ≠ pair i k := by
    intro he
    rw [he,sub_self] at hk
    have hz : wordWeight (0 : W).val = 0 := by decide
    omega
  have h := hw _ ht _ hne
  omega
end BinaryPermutation.SixCoreWeightFour
