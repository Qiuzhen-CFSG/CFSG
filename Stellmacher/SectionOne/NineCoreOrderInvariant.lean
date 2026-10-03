module

public import Theory.GroupTheory.IrreducibleKleinComplementExclusion
public import Theory.GroupTheory.NormalizedSupCard
public import Stellmacher.SectionOne.Defs

/-!
# Invariant subgroups of a nine-core with a maximal four-complement

A normal subgroup of order nine and a subgroup of order four intersect
trivially. If they generate the ambient finite group and the latter is a
coatom, any invariant subgroup of the former is trivial or the whole
normal subgroup: its join with the complement is either the complement
or the whole group, and product counting settles the second case.

With trivial two-core, the complement is core-free. The general exclusion
of an elementary-four core-free irreducible complement then gives the
contradiction needed in the order-thirty-six branch of Stellmacher (9.1)(8),
printed p.47 of `refs/files/stellmacher-n-group.pdf`.

The invariant-subgroup argument does not require elementary abelian
structure or Sylow maximality. The final wrapper supplies core-freeness
from the standing Section One hypotheses, rather than assuming it from
the generated product alone.
-/

namespace Stellmacher.SectionOne

universe u

public theorem nineCore_invariant_eq_bot_or_eq_of_coatom
    {K : Type u} [Group K] [Finite K]
    (W R : Subgroup K) [W.Normal]
    (hWcard : Nat.card W = 9) (hRcard : Nat.card R = 4)
    (hgen : W ⊔ R = ⊤) (hmax : IsCoatom R)
    (A : Subgroup K) (hAW : A ≤ W)
    (hstable : ∀ t : R, ∀ a : K, a ∈ A → (t : K) * a * (t : K)⁻¹ ∈ A) :
    A = ⊥ ∨ A = W := by
  classical
  have hdis : Disjoint W R :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hWcard, hRcard]; decide)
  have hnorm : R ≤ Subgroup.normalizer (A : Set K) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro t ht a ha
    exact hstable ⟨t, ht⟩ a ha
  rcases hmax.le_iff.mp (show R ≤ A ⊔ R from le_sup_right) with htop | heq
  · right
    have hcardA := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes A R hnorm
    have hcardW := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes W R
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    have hAR : A ⊓ R = ⊥ := (hdis.mono_left hAW).eq_bot
    rw [hAR, Subgroup.card_bot, one_mul, htop] at hcardA
    rw [hdis.eq_bot, Subgroup.card_bot, one_mul, hgen] at hcardW
    have hcard : Nat.card A = Nat.card W := by
      rw [hRcard] at hcardA hcardW
      omega
    let _ : Fintype A := Fintype.ofFinite A
    let _ : Fintype W := Fintype.ofFinite W
    apply SetLike.coe_injective
    exact Set.eq_of_subset_of_card_le hAW (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hcard.ge)
  · left
    apply bot_unique
    have hAR : A ≤ R := le_sup_left.trans_eq heq
    exact (le_inf hAW hAR).trans hdis.le_bot

public theorem nineCore_not_elementary_four_coatom_of_twoCore_eq_bot
    {K : Type u} [Group K] [Finite K]
    (W R : Subgroup K) [W.Normal] [IsElementaryAbelian 2 R]
    (hcore : pCore 2 K = ⊥)
    (hWcard : Nat.card W = 9) (hRcard : Nat.card R = 4)
    (hgen : W ⊔ R = ⊤) (hmax : IsCoatom R) : False := by
  have hRp : IsPGroup 2 R := IsPGroup.iff_card.mpr ⟨2, hRcard⟩
  have hcorep : IsPGroup 2 R.normalCore :=
    hRp.of_injective (Subgroup.inclusion R.normalCore_le)
      (Subgroup.inclusion_injective R.normalCore_le)
  have hRcore : R.normalCore = ⊥ := by
    apply bot_unique
    have hle : R.normalCore ≤ pCore 2 K := le_sSup ⟨inferInstance, hcorep⟩
    exact hle.trans_eq hcore
  exact Theory.GroupTheory.not_elementary_four_corefree_irreducible_complement
    W R hRcard hgen hRcore
    (nineCore_invariant_eq_bot_or_eq_of_coatom W R hWcard hRcard hgen hmax)

public theorem nineCore_not_elementary_four_coatom
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (R : Sylow 2 K)
    (hR : IsElementaryAbelian 2 (R : Subgroup K))
    (hRcard : Nat.card (R : Subgroup K) = 4)
    (hgen : oddCore K ⊔ (R : Subgroup K) = ⊤)
    (hWcard : Nat.card (oddCore K) = 9)
    (hmax : IsCoatom (R : Subgroup K)) : False := by
  let _ : IsElementaryAbelian 2 (R : Subgroup K) := hR
  let _ : (oddCore K).Normal := pPrimeCore_normal
  exact nineCore_not_elementary_four_coatom_of_twoCore_eq_bot
    (oddCore K) (R : Subgroup K) h.twoCore_eq_bot hWcard hRcard hgen hmax

end Stellmacher.SectionOne
