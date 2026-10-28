module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Rank-one reduction of the actual C.2.7 component

The source center has order one or three. Three-rank at most one makes a
Sylow three-subgroup cyclic, and perfect central transfer removes the cubic
possibility. The literal map from K/O₂(K) to K* is therefore an isomorphism.

The C.2.7 star catalogue then reduces to SL₂ over a binary field. Concrete
cubic-rank witnesses exclude Sp₄, G₂, their small derived rows, SL₅(2), and
A₆–A₈. The triple cover is not centerless. In the SL₃ row, low three-rank
forces odd field degree, whose general linear order is prime to five.
The original factor of five thus excludes that final row. No five-rank
bound, universal embedding classification, or auxiliary model is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the C.2.7
comparison in the proof of 10.2.6, pp.748–749, with C.2.7, pp.145–147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter1.RadicalExclusions.ModelReduction FullSieve SourceInterface
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- The only possible scalar kernel disappears under the actual cubic-rank bound. -/
theorem source_rank_one_coreQuotient_center
    (h : Input KnownSimple.IsKnownSimple H R M K) (hr : primeRank 3 K ≤ 1) :
    center (K ⧸ pCore 2 K) = ⊥ := by
  let Q := K ⧸ pCore 2 K
  let : IsQuasisimple Q := h.quasisimple
  have hrQ : primeRank 3 Q ≤ 1 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup).trans hr
  let P : Sylow 3 Q := default
  let := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hrQ
  have hnot := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow
    (QuotientGroup.mk' (center Q)) (by rw [QuotientGroup.ker_mk']) P inferInstance
  rw [QuotientGroup.ker_mk'] at hnot
  rcases coreQuotient_center_card_from_source h with hc | hc
  · exact (eq_bot_iff_card _).mpr hc
  · exact (hnot (hc ▸ dvd_rfl)).elim

/-- The isomorphism is the literal source comparison map, with no change of quotient. -/
@[expose] def source_rank_one_coreToStar_equiv
    (h : Input KnownSimple.IsKnownSimple H R M K) (hr : primeRank 3 K ≤ 1) :
    (K ⧸ pCore 2 K) ≃* starImage K R K :=
  MulEquiv.ofBijective (coreToStar h.normalizes) ⟨
    (MonoidHom.ker_eq_bot_iff _).mp (bot_unique
      ((coreToStar_ker_central_from_source h).trans_eq
        (source_rank_one_coreQuotient_center h hr))),
    coreToStar_surjective h.normalizes⟩

/-- The comparison isomorphism retains the original quotient homomorphism. -/
@[simp] theorem source_rank_one_coreToStar_equiv_apply
    (h : Input KnownSimple.IsKnownSimple H R M K) (hr : primeRank 3 K ≤ 1)
    (x : K ⧸ pCore 2 K) :
    source_rank_one_coreToStar_equiv h hr x = coreToStar h.normalizes x := rfl

/-- The original map K → K* has exactly its two-core as kernel. -/
theorem source_rank_one_toStarImage_kernel
    (h : Input KnownSimple.IsKnownSimple H R M K) (hr : primeRank 3 K ≤ 1) :
    (toStarImage K R).ker = pCore 2 K := by
  apply le_antisymm _ (core_le_toStarImage_ker h.normalizes)
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply (source_rank_one_coreToStar_equiv h hr).injective
  change coreToStar h.normalizes (QuotientGroup.mk' (pCore 2 K) x) =
    coreToStar h.normalizes 1
  rw [coreToStar_mk, map_one]
  exact hx

private theorem two_pow_odd_mod_five (n : ℕ) (hn : Odd n) :
    2 ^ n % 5 = 2 ∨ 2 ^ n % 5 = 3 := by
  have hn2 := Nat.odd_iff.mp hn
  have hn4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  have he : n = 4 * (n / 4) + n % 4 := by omega
  rw [he, pow_add, pow_mul, Nat.mul_mod]
  have hpow : (2 ^ 4) ^ (n / 4) % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [hpow]
  rcases hn4 with h | h <;> rw [h] <;> norm_num

private theorem linear_three_not_five (F : BinaryField)
    (hr : primeRank 3 SL(3,F.Carrier) ≤ 1) : ¬5 ∣ Nat.card SL(3,F.Carrier) := by
  have ho : Odd F.degree := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hh := Theory.SpecificGroups.SignedThreeCubicRank.linear_special F.card_eq he
    omega
  let q := Nat.card F.Carrier
  have hq : q % 5 = 2 ∨ q % 5 = 3 := by
    rw [show q = 2 ^ F.degree from F.card_eq]
    exact two_pow_odd_mod_five _ ho
  have hqpos : 1 ≤ q := Nat.card_pos
  have h1 : 1 ≤ q ^ 3 := one_le_pow₀ hqpos
  have h2 : q ≤ q ^ 3 := by simpa using Nat.pow_le_pow_right hqpos (by decide : 1 ≤ 3)
  have h3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hqpos (by decide : 2 ≤ 3)
  have hsub1 := Nat.sub_add_cancel h1
  have hsub2 := Nat.sub_add_cancel h2
  have hsub3 := Nat.sub_add_cancel h3
  have ha : ¬5 ∣ q ^ 3 - 1 := by
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hm := congrArg (fun n => n % 5) hsub1
    rw [Nat.add_mod, Nat.pow_mod] at hm
    rcases hq with hh | hh <;> rw [hh] at hm <;> norm_num at hm <;> omega
  have hb : ¬5 ∣ q ^ 3 - q := by
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hm := congrArg (fun n => n % 5) hsub2
    rw [Nat.add_mod, Nat.pow_mod] at hm
    rcases hq with hh | hh <;> rw [hh] at hm <;> norm_num at hm <;> omega
  have hc : ¬5 ∣ q ^ 3 - q ^ 2 := by
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hm := congrArg (fun n => n % 5) hsub3
    rcases hq with hh | hh <;> norm_num [Nat.add_mod, Nat.pow_mod, hh, hz] at hm
  intro hd
  have hgl := hd.trans (card_dvd_of_injective
    (Matrix.SpecialLinearGroup.toGL : SL(3,F.Carrier) →* GL (Fin 3) F.Carrier)
    Matrix.SpecialLinearGroup.toGL_injective)
  let : Fintype F.Carrier := Fintype.ofFinite _
  have hcard : Nat.card (GL (Fin 3) F.Carrier) = (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) := by
    simpa [Nat.card_eq_fintype_card, q, Fin.prod_univ_succ, mul_assoc] using
      Matrix.card_GL_field (𝔽 := F.Carrier) 3
  rw [hcard] at hgl
  rcases (by decide : Nat.Prime 5).dvd_mul.mp hgl with hab | hc'
  · exact ((by decide : Nat.Prime 5).dvd_mul.mp hab).elim ha hb
  · exact hc hc'

private def alternatingFiveLinearEquiv :
    alternatingGroup (Fin 5) ≃* SL(2,BinaryField.four.Carrier) :=
  (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := BinaryField.four.Carrier) (by
      change Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by decide)]
      decide)).some.symm.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm

private theorem rank_one_star_model {A : Type*} [Group A] [Finite A]
    (h : StarModels.Model A) (hr : primeRank 3 A ≤ 1)
    (hz : center A = ⊥) (hfive : 5 ∣ Nat.card A) :
    ∃ F : BinaryField, Nonempty (A ≃* SL(2,F.Carrier)) := by
  cases h with
  | linearTwo F e => exact ⟨F,⟨e⟩⟩
  | linearThree F e =>
    have hr' : primeRank 3 SL(3,F.Carrier) ≤ 1 := (primeRank_equiv 3 e) ▸ hr
    exact (linear_three_not_five F hr' ((Nat.card_congr e.toEquiv) ▸ hfive)).elim
  | symplectic F _ e =>
    have hl := (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic (F := F.Carrier)).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Matrix.symplecticGroup (Fin 2) F.Carrier)).subtype Subtype.val_injective)
    rw [←primeRank_equiv 3 e] at hl
    omega
  | g2 F _ e =>
    have hl := (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := F.Carrier)).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Atlas.G2.Model F.Carrier)).subtype Subtype.val_injective)
    rw [←primeRank_equiv 3 e] at hl
    omega
  | g2DerivedTwo e =>
    have hl := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := ZMod 2)
    rw [←primeRank_equiv 3 e] at hl
    omega
  | alternating n hn e =>
    have hnlt : n < 6 := by
      by_contra! hh
      have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank hh
      rw [←primeRank_equiv 3 e] at hl
      omega
    have hn5 : n = 5 := by rcases hn with hn | hn | hn | hn <;> omega
    subst n
    exact ⟨BinaryField.four,⟨e.trans alternatingFiveLinearEquiv⟩⟩
  | linearFiveTwo e =>
    have hl := Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank (by decide : 4 ≤ 5)
    rw [←primeRank_equiv 3 e] at hl
    omega
  | tripleSix e _ =>
    have hc : Nat.card (center A) = 3 := by
      rw [Nat.card_congr e.toEquiv]
      exact Nat.card_zmod 3
    rw [hz, card_bot] at hc
    omega

/-- The actual C.2.7 input, the cubic-rank bound and the original factor five
force a rank-one binary model for the literal two-core quotient. -/
theorem source_rank_one_coreQuotient_linearTwo
    (h : Input KnownSimple.IsKnownSimple H R M K) (hr : primeRank 3 K ≤ 1)
    (hfive : 5 ∣ Nat.card (K ⧸ pCore 2 K)) :
    ∃ F : BinaryField, Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,F.Carrier)) := by
  let e := source_rank_one_coreToStar_equiv h hr
  have hrQ : primeRank 3 (K ⧸ pCore 2 K) ≤ 1 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup).trans hr
  have hrS : primeRank 3 (starImage K R K) ≤ 1 := (primeRank_equiv 3 e) ▸ hrQ
  have hc : Nat.card (center (starImage K R K)) = 1 := by
    rw [←Nat.card_congr (centerCongr e).toEquiv,
      source_rank_one_coreQuotient_center h hr,card_bot]
  have hfiveS : 5 ∣ Nat.card (starImage K R K) := (Nat.card_congr e.toEquiv) ▸ hfive
  obtain ⟨F,⟨eF⟩⟩ := rank_one_star_model (star_model_from_source h) hrS
    ((eq_bot_iff_card _).mpr hc) hfiveS
  exact ⟨F,⟨e.trans eF⟩⟩

end CFSG.Quasithin.Chapter10
