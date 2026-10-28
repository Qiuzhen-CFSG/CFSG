module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.QuotientTransport
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.Mathieu.M24.Properties.Simplicity
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Inner action on the L₄(2) section embedded in M₂₄

The E₁₆-by-L₄(2) subgroup in A.3.12(14) has order 322560 and odd index
759 in M₂₄. Every ambient automorphism is inner, and the trivial center
makes its conjugator have the same order. A two-element normalizing an
odd-index subgroup belongs to that subgroup, by the odd order of the
relative normalizer quotient. This supplies inner action modulo O₂(A).

The other branches of A.3.12(14) have orders 10752, 69120 and 21504.
None is divisible by 20160, the order of the supplied section A/O₂(A).
Thus the full three-way disjunction selects the required extension without
an additional recognition or stabilizer hypothesis. The proof uses the
actual ambient isomorphism to the Witt-design M₂₄ and retains the normal
extension kernel; no splitting or assumption O₂(A) = 1 is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.12(14),
printed pp.47–48, and the proof of Lemma 1.3.9(1), printed p.514.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.MathieuTwentyFourStabilizer
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open Sporadic.Mathieu

variable {G : Type*} [Group G]

private theorem card_linear_four (h : ClassicalGroup.IsPSL G 4 2) :
    Nat.card G = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

private theorem card_linear_three (h : ClassicalGroup.IsPSL G 3 2) :
    Nat.card G = 168 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

private theorem card_elementary (r : ℕ) (h : ElementaryModel 2 r G) :
    Nat.card G = 2 ^ r := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp

private theorem card_cover_six (h : IsAlternatingCover G 6) :
    Nat.card G = 1080 := by
  obtain ⟨_, ⟨ez⟩, ⟨eq⟩⟩ := h
  rw [card_eq_card_quotient_mul_card_subgroup (center G),
    Nat.card_congr eq.toEquiv, Nat.card_congr ez.toEquiv, nat_card_alternatingGroup]
  norm_num

/-- The extension in the L₄(2) branch has the full two-part of |M₂₄|. -/
theorem card_of_extension
    (h : HasExtension G (ElementaryModel 2 4) (fun Z _ => ClassicalGroup.IsPSL Z 4 2)) :
    Nat.card G = 322560 := by
  obtain ⟨N, _, hN, hQ⟩ := h
  rw [card_eq_card_quotient_mul_card_subgroup N, card_linear_four hQ,
    card_elementary 4 hN]
  norm_num

/-- The supplied intrinsic section excludes every other small-subgroup branch
of A.3.12(14), including the nonsplit triple-cover alternative. -/
theorem extension_of_fourteen (A : Subgroup G)
    (hsection : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hsmall :
      HasExtension A (ElementaryModel 2 4) (fun Z _ => ClassicalGroup.IsPSL Z 4 2) ∨
      HasExtension A (ElementaryModel 2 6)
        (fun Z _ => ClassicalGroup.IsPSL Z 3 2 ∨ IsAlternatingCover Z 6) ∨
      HasExtension A (ExtraspecialModel 2 3) (fun Z _ => ClassicalGroup.IsPSL Z 3 2)) :
    HasExtension A (ElementaryModel 2 4) (fun Z _ => ClassicalGroup.IsPSL Z 4 2) := by
  have hdiv : 20160 ∣ Nat.card A := by
    rw [← card_linear_four hsection]
    exact card_quotient_dvd_card (pCore 2 A)
  rcases hsmall with h | h | h
  · exact h
  · obtain ⟨N, _, hN, hQ⟩ := h
    rw [card_eq_card_quotient_mul_card_subgroup N, card_elementary 6 hN] at hdiv
    rcases hQ with hQ | hQ
    · rw [card_linear_three hQ] at hdiv
      norm_num at hdiv
    · rw [card_cover_six hQ] at hdiv
      norm_num at hdiv
  · obtain ⟨N, _, hN, hQ⟩ := h
    rw [card_eq_card_quotient_mul_card_subgroup N, card_linear_three hQ, hN.2] at hdiv
    norm_num at hdiv

private theorem m24_center : center M24 = ⊥ := by
  let := m24_isSimpleGroup
  rcases (inferInstance : (center M24).Normal).eq_bot_or_eq_top with h | h
  · exact h
  let := Group.commGroupOfCenterEqTop h
  have hp := IsSimpleGroup.prime_card (α := M24)
  rw [m24_order] at hp
  norm_num at hp

private theorem mem_of_odd_index [Finite G] (A : Subgroup G)
    (hodd : Odd A.index) (g : G) (hgN : g ∈ normalizer (A : Set G))
    (n : ℕ) (hg : g ^ (2 ^ n) = 1) : g ∈ A := by
  let N := normalizer (A : Set G)
  let B := A.subgroupOf N
  let q := QuotientGroup.mk' B
  have hcard : Odd (Nat.card (N ⧸ B)) :=
    hodd.of_dvd_nat (relIndex_dvd_index_of_le A.le_normalizer)
  have hpow : q ⟨g, hgN⟩ ^ (2 ^ n) = 1 := by
    rw [← map_pow]
    have he : (⟨g, hgN⟩ : N) ^ (2 ^ n) = 1 := Subtype.ext hg
    rw [he, map_one]
  have he : q ⟨g, hgN⟩ = 1 :=
    (hcard.coprime_two_right.pow_right n).pow_left_bijective.injective (by simpa using hpow)
  change (⟨g, hgN⟩ : N) ∈ B
  exact (QuotientGroup.eq_one_iff _).mp he

private theorem concrete_of_odd_index (A : Subgroup M24) (hodd : Odd A.index) :
    TwoStabilizerActsInner A := by
  intro α ⟨n, hn⟩ hα
  obtain ⟨g, rfl⟩ := M24OuterRestriction.conj_surjective α
  have hgN : g ∈ normalizer (A : Set M24) := mem_normalizer_iff_map_conj_eq.mpr hα
  have hpow : g ^ (2 ^ n) = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot m24_center
    rw [map_pow, hn, map_one]
  have hg := mem_of_odd_index A hodd g hgN n hpow
  refine ⟨g, hg, fun x _ => ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

/-- Two-power-order ambient automorphisms preserving the actual extension
act by inner automorphisms on its intrinsic two-core quotient. -/
theorem twoStabilizerActsInner {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* M24) (A : Subgroup Q)
    (hext : HasExtension A (ElementaryModel 2 4) (fun Z _ => ClassicalGroup.IsPSL Z 4 2)) :
    TwoStabilizerActsInner A := by
  apply TwoStabilizerActsInner.of_map e
  apply concrete_of_odd_index
  have hc : Nat.card (A.map e.toMonoidHom) = 322560 := by
    rw [card_map_of_injective e.injective]
    exact card_of_extension hext
  have hi := card_mul_index (A.map e.toMonoidHom)
  rw [hc, m24_order] at hi
  have hi' : (A.map e.toMonoidHom).index = 759 := by omega
  rw [hi']
  decide

/-- Assembly from all the small-subgroup alternatives in A.3.12(14).
Branch selection is discharged using the specified L₄(2) section. -/
theorem twoStabilizerActsInner_of_fourteen {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* M24) (A : Subgroup Q)
    (hsection : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hsmall :
      HasExtension A (ElementaryModel 2 4) (fun Z _ => ClassicalGroup.IsPSL Z 4 2) ∨
      HasExtension A (ElementaryModel 2 6)
        (fun Z _ => ClassicalGroup.IsPSL Z 3 2 ∨ IsAlternatingCover Z 6) ∨
      HasExtension A (ExtraspecialModel 2 3) (fun Z _ => ClassicalGroup.IsPSL Z 3 2)) :
    TwoStabilizerActsInner A :=
  twoStabilizerActsInner e A (extension_of_fourteen A hsection hsmall)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.MathieuTwentyFourStabilizer
