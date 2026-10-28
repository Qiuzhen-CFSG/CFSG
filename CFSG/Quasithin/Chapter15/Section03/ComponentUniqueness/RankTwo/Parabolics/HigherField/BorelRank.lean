module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Models
public import Theory.SpecificGroups.PSL3.LinearThreeBorelOrder
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.Fitting.Core

/-!
# The PSL₃(4) Borel obstruction, including central two-covers

An actual projective Borel over F₄ has order 192. Sylow conjugacy transfers
that calculation to every Sylow normalizer of a group isomorphic to PSL₃(4).
Consequently those normalizers have three-rank one.

For a surjection with two-group kernel, the original Sylow normalizer maps
into the image Sylow normalizer and its kernel has three-rank zero. The
rank bound therefore also holds upstairs. Since O(L) = 1 puts Z(L) inside
O₂(L), this handles every central cover of PSL₃(4) with trivial odd core.
It does not assert the stronger, unjustified implication Z(L) = 1.

These are the last rank and cover steps needed in the larger-field paragraph
of the proof of 15.3.35. The selection of PSL₃(2ⁿ) and the deduction n = 2
remain separate obligations.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed p.1139;
the concrete Borel count is in Theory.SpecificGroups.PSL3.LinearThreeBorelOrder.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Matrix.PSL3.LinearThree

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField

private theorem rank_le_one_of_not_nine {K : Type*} [Group K] [Finite K]
    (hc : ¬ 9 ∣ Nat.card K) : primeRank 3 K ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le K).mpr
  intro E hE
  obtain ⟨n, hn⟩ := hE.isPGroup.exists_card_eq
  have hn1 : n ≤ 1 := by
    by_contra! h
    exact hc ((hn ▸ pow_dvd_pow 3 (by omega : 2 ≤ n)).trans E.card_subgroup_dvd_card)
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hn1

/-- Every marked Sylow normalizer in the actual PSL₃(4) model has order 192. -/
theorem card_normalizer_psl3_four {K : Type*} [Group K] [Finite K]
    (hmodel : ClassicalGroup.IsPSL K 3 4) (P : Sylow 2 K) :
    Nat.card (normalizer (P : Set K)) = 192 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let U := unipotentSylow F (by decide : 0 < 2) hF
  let T := U.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T P
  let f := e.symm.trans (MulAut.conj g)
  have hP : (unipotent F).map f.toMonoidHom = (P : Subgroup K) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((unipotent F).map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hh
    change (unipotent F).map ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    rwa [← map_map]
  have hN : (borel F).map f.toMonoidHom = normalizer (P : Set K) := by
    rw [← normalizer_unipotent F (by decide : 0 < 2) hF, map_equiv_normalizer_eq, hP]
    rfl
  rw [← hN, card_map_of_injective f.injective]
  exact Matrix.PSL3.CartanActions.BorelQuotient.card_borel_linear_three_four F hF

/-- The concrete order bound gives three-rank at most one. -/
theorem three_rank_normalizer_psl3_four_le_one {K : Type*} [Group K] [Finite K]
    (hmodel : ClassicalGroup.IsPSL K 3 4) (P : Sylow 2 K) :
    primeRank 3 (normalizer (P : Set K)) ≤ 1 := by
  apply rank_le_one_of_not_nine
  rw [card_normalizer_psl3_four hmodel P]
  decide

/-- Three divides 192, so the standard Borel bound is attained. -/
theorem three_rank_normalizer_psl3_four {K : Type*} [Group K] [Finite K]
    (hmodel : ClassicalGroup.IsPSL K 3 4) (P : Sylow 2 K) :
    primeRank 3 (normalizer (P : Set K)) = 1 := by
  have hle := three_rank_normalizer_psl3_four_le_one hmodel P
  have hne : primeRank 3 (normalizer (P : Set K)) ≠ 0 := by
    intro hz
    have hn := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    rw [card_normalizer_psl3_four hmodel P] at hn
    exact hn (by decide)
  omega

private theorem rank_normalizer_cover {K H : Type*} [Group K] [Finite K]
    [Group H] [Finite H] (f : K →* H) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hmodel : ClassicalGroup.IsPSL H 3 4)
    (P : Sylow 2 K) : primeRank 3 (normalizer (P : Set K)) ≤ 1 := by
  let Q := P.mapSurjective hf
  let N := normalizer (P : Set K)
  let fN : N →* normalizer (Q : Set H) :=
    (f.comp N.subtype).codRestrict _ (fun x =>
      (P : Subgroup K).le_normalizer_map f (mem_map_of_mem f x.property))
  let k : fN.ker →* f.ker :=
    ((N.subtype.comp fN.ker.subtype).codRestrict _ (fun x =>
      congrArg Subtype.val x.property))
  have hki : Function.Injective k := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : K)) h))
  have hkt : IsPGroup 2 fN.ker := IsPGroup.of_injective hk k hki
  have hkr : primeRank 3 fN.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n, hn⟩ := hkt.exists_card_eq
    rw [hn]
    intro hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hr := primeRank_le_ker_add (p := 3) fN
  rw [hkr, zero_add] at hr
  exact hr.trans (three_rank_normalizer_psl3_four_le_one hmodel Q)

/-- The rank bound survives all central covers with trivial odd core.
No centerlessness or multiplier premise is required. -/
theorem three_rank_normalizer_central_cover_le_one {K : Type*} [Group K] [Finite K]
    (hodd : pPrimeCore 2 K = ⊥)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 3 4) (P : Sylow 2 K) :
    primeRank 3 (normalizer (P : Set K)) ≤ 1 := by
  have hcenter : center K ≤ pCore 2 K := by
    have hc : center K ≤ fittingSubgroup K := le_sSup ⟨inferInstance, inferInstance⟩
    exact hc.trans (Fitting_eq_pcore K 2 hodd).le
  apply rank_normalizer_cover (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _) _ hmodel P
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup.to_le hcenter

/-- The bound for the literal Borel inside the original component. -/
theorem three_rank_borel_central_cover_le_one {G : Type*} [Group G] [Finite G]
    (L S B : Subgroup G) (hB : BorelOverSylow L S B)
    (hodd : pPrimeCore 2 L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) : primeRank 3 B ≤ 1 := by
  obtain ⟨P, _, rfl⟩ := hB
  rw [← primeRank_equiv 3 ((normalizer (P : Set L)).equivMapOfInjective
    L.subtype L.subtype_injective)]
  exact three_rank_normalizer_central_cover_le_one hodd hmodel P

/-- A rank-two actor in that Borel is impossible, even in a nontrivial
central two-cover of the projective group. -/
theorem no_rank_two_actor_in_psl3_four_borel {G : Type*} [Group G] [Finite G]
    (L Yplus S B : Subgroup G) (hB : BorelOverSylow L S B)
    (hYB : Yplus ≤ B) (hrank : 2 ≤ primeRank 3 Yplus)
    (hodd : pPrimeCore 2 L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) : False := by
  have hbound := (primeRank_le_of_injective 3 (inclusion hYB)
    (inclusion_injective hYB)).trans
    (three_rank_borel_central_cover_le_one L S B hB hodd hmodel)
  omega

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField
