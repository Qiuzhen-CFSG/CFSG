module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CubicCentralizer
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The involutory splitting of the original cubic normalizer

The faithful quotient N_H(A)/C_H(A) acts on the order-three subgroup A,
so its order is at most two. The recorded element outside the centralizer
makes the action onto Aut(A). Its square-one equation then gives the literal
factorization N_H(A) = C_H(A)⟨s⟩, with the same splitting element.

This is the normalizer structure used in AS91 (8.3), p.606, from the concrete
(4.9) input. It is proved in the original H, retaining both central factors.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))
variable (s : centralizer z) (hs : s ∈ cubicNormalizerInH e X)
variable (hsC : s ∉ cubicCentralizerInH e X)
include h hs hsC

theorem cubicNormalizer_action_surjective :
    Function.Surjective (cubicSylowImage e X).normalizerMonoidHom := by
  let A := cubicSylowImage e X
  let : IsCyclic A := isCyclic_of_prime_card (cubicSylowImage_card h e X)
  have hcard : Nat.card (MulAut A) = 2 := by
    rw [IsCyclic.card_mulAut, cubicSylowImage_card h e X]
    decide
  let : Fact (Nat.card (MulAut A)).Prime := ⟨hcard ▸ Nat.prime_two⟩
  apply MonoidHom.range_eq_top.mp
  rcases A.normalizerMonoidHom.range.eq_bot_or_eq_top_of_prime_card with hb | ht
  · have h1 : A.normalizerMonoidHom ⟨s,hs⟩ = 1 :=
      hb.le ⟨⟨s,hs⟩,rfl⟩
    have hm : (⟨s,hs⟩ : cubicNormalizerInH e X) ∈ A.normalizerMonoidHom.ker := h1
    rw [normalizerMonoidHom_ker] at hm
    exact (hsC hm).elim
  · exact ht

theorem cubicNormalizer_card :
    Nat.card (cubicNormalizerInH e X) = 2 * Nat.card (cubicCentralizerInH e X) := by
  let A := cubicSylowImage e X
  let : IsCyclic A := isCyclic_of_prime_card (cubicSylowImage_card h e X)
  have hc := A.normalizerMonoidHom.ker.card_mul_index
  rw [index_eq_card, Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective A.normalizerMonoidHom
      (cubicNormalizer_action_surjective h e X s hs hsC)).toEquiv,
    IsCyclic.card_mulAut, cubicSylowImage_card h e X, normalizerMonoidHom_ker,
    Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set (centralizer z)))).toEquiv] at hc
  simpa only [show Nat.totient 3 = 2 from rfl, Nat.mul_comm] using hc.symm

/-- The supplied involution gives an actual split normalizer in the original H. -/
theorem cubicNormalizer_eq_sup (hs2 : s * s = 1) :
    cubicNormalizerInH e X = cubicCentralizerInH e X ⊔ zpowers s := by
  apply (eq_of_le_of_card_ge
    (sup_le (centralizer_le_normalizer _) (zpowers_le.mpr hs)) ?_).symm
  rw [card_sup_zpowers_of_normalizing_involution (cubicCentralizerInH e X) s
    (by simpa only [pow_two] using hs2) hsC
    (normalizer_le_normalizer_centralizer (cubicSylowImage e X) hs),
    cubicNormalizer_card h e X s hs hsC]

/-- The factorization uses precisely the recorded splitting element. -/
theorem cubicNormalizer_exists_mul (hs2 : s * s = 1) (n : cubicNormalizerInH e X) :
    ∃ c : cubicCentralizerInH e X, n.val = c.val ∨ n.val = c.val * s := by
  classical
  have hn : n.val ∈ cubicCentralizerInH e X ⊔ zpowers s :=
    cubicNormalizer_eq_sup h e X s hs hsC hs2 ▸ n.property
  have hn' : n.val ∈ (cubicCentralizerInH e X : Set (centralizer z)) *
      (zpowers s : Set (centralizer z)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      (zpowers_le.mpr (normalizer_le_normalizer_centralizer (cubicSylowImage e X) hs))]
    exact hn
  obtain ⟨c,hc,k,hk,hck⟩ := hn'
  have hsne : s ≠ 1 := fun he => hsC (he ▸ one_mem _)
  have horder : orderOf s = 2 := orderOf_eq_prime (by simpa only [pow_two] using hs2) hsne
  have hfin : IsOfFinOrder s := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨2,by decide,by simpa only [pow_two] using hs2⟩
  change k ∈ zpowers s at hk
  rw [hfin.mem_zpowers_iff_mem_range_orderOf,horder] at hk
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  refine ⟨⟨c,hc⟩,?_⟩
  rcases hi' with rfl | rfl
  · exact Or.inl (by simpa only [pow_zero,mul_one] using hck.symm)
  · exact Or.inr (by simpa only [pow_one] using hck.symm)

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
