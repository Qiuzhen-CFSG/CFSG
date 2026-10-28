module

public import Theory.Quasithin.CentralExtensionRankFour
public import Theory.SpecificGroups.Classical.LinearRankFourCentralizer
public import Theory.SpecificGroups.SL2.CommutingUnipotents
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Descent

/-!
# Defining-center obstructions for the first two A.2.17 model branches

The rank-four central-extension theorem applies inside the original group's
lifted involution centralizer. For an actual PSL_n(r^e) central quotient,
quasithinness and an odd center force n ≤ 4, uniformly in all positive field
degrees, including q = 3 and q = 9. The defining-r-center corollary uses the
original IsPSL model marking and obtains oddness from the actual center.

For the actual odd triality carrier, the marked commuting fundamental
SL₂(q) and complementary SL₂(q³) maps give an elementary subgroup of order
q⁴ in the scalar involution centralizer. This contradicts quasithinness
through any odd central kernel. The odd pinned maps, their quotient
faithfulness, and commutation are precisely the earlier model inputs still
retained by OddFundamentalCentralizer; they are not rank-witness assumptions.
The model producer must discharge them in final assembly.

These are partial source branches, not the uniform O_r(G) = 1 theorem.
The PSL degrees three and four, all unitary/symplectic/orthogonal ranges,
and the remaining exceptional families still require their source arguments.
In particular no quotient SQTK hypothesis or preclassification multiplier
table is used. These direct obstructions need neither K-group induction nor
quasisimplicity, so they apply in particular under all the original source
hypotheses supplied by the A.2 assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, A.2.13–15 and A.2.17, printed pp.37–40.
The book's defining-center branch is Case II of A.2.13.
-/

public section

open Matrix Subgroup
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterA.Section02.OddLie.DefiningKernel

variable {G : Type*} [Group G] [Finite G]

theorem not_quasithin_linear_cover {F : Type*} [Field F] [Finite F]
    {r e d : ℕ} [Fact r.Prime] [CharP F r] (hr : r ≠ 2) (he : 1 ≤ e)
    (hd : 0 < d) (hF : Nat.card F = r ^ e)
    (iso : (G ⧸ center G) ≃* PSL(4 + d,F))
    (ho : Odd (Nat.card (center G))) : ¬ IsQuasithin G := by
  let : IsElementaryAbelian r (Multiplicative (Matrix (Fin 2) (Fin 2) F)) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (SpecialLinearGroup.LinearRankFourCentralizer.elementary_exponent F r) }
  apply CentralExtension.not_isQuasithin_of_center_quotient_model iso ho hr
    (SpecialLinearGroup.LinearRankFourCentralizer.involution_order F hr hd)
    (SpecialLinearGroup.LinearRankFourCentralizer.elementaryCentralizer F d)
    (SpecialLinearGroup.LinearRankFourCentralizer.elementaryCentralizer_injective F hd)
  rw [SpecialLinearGroup.LinearRankFourCentralizer.elementary_card F hF]
  exact pow_le_pow_right' (Fact.out : r.Prime).one_lt.le (by omega)

theorem linear_degree_le_four_of_odd_center {r e n : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 1 ≤ e) (hG : IsQuasithin G)
    (ho : Odd (Nat.card (center G)))
    (model : ClassicalGroup.IsPSL (G ⧸ center G) n (r ^ e)) : n ≤ 4 := by
  obtain ⟨F, hF, hfin, hcard, ⟨iso⟩⟩ := model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  by_contra hn
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 < d ∧ n = 4 + d := ⟨n - 4, by omega, by omega⟩
  exact not_quasithin_linear_cover hr he hd hcard iso ho hG

theorem linear_degree_le_four_of_defining_center {r e n : ℕ} [Fact r.Prime]
    (hr : Odd r) (he : 1 ≤ e) (hG : IsQuasithin G)
    (hc : IsPGroup r (center G))
    (model : ClassicalGroup.IsPSL (G ⧸ center G) n (r ^ e)) : n ≤ 4 := by
  apply linear_degree_le_four_of_odd_center
    (by rintro rfl; exact (by decide : ¬ Odd 2) hr) he hG _ model
  obtain ⟨k, hk⟩ := hc.exists_card_eq
  rw [hk]
  exact hr.pow

open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.OddFundamentalCentralizer

theorem not_quasithin_triality_cover {P : Parameters}
    (hr : Odd P.prime) (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)
    (hk : Function.Injective (fundamentalHom D))
    (hj : Function.Injective (complementHom D C))
    (hcomm : ∀ a b, Commute (fundamentalHom D a) (complementHom D C b))
    (iso : (G ⧸ center G) ≃* Carrier P)
    (ho : Odd (Nat.card (center G))) : ¬ IsQuasithin G := by
  let : IsElementaryAbelian P.prime
      (Multiplicative (GaloisField P.prime P.exponent) × Multiplicative (ExtensionField P)) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (SpecialLinearGroup.CommutingUnipotents.pair_exponent P.prime) }
  have hp : P.prime ≠ 2 := by rintro he; exact (by decide : ¬ Odd 2) (he ▸ hr)
  obtain ⟨hz, hz2⟩ := SpecialLinearGroup.map_neg_one_isInvolution hp (fundamentalHom D) hk
  apply CentralExtension.not_isQuasithin_of_center_quotient_model iso ho hp
    (orderOf_eq_prime hz2 hz)
    (SpecialLinearGroup.CommutingUnipotents.centralizerPair
      (fundamentalHom D) (complementHom D C) hcomm)
    (SpecialLinearGroup.CommutingUnipotents.centralizerPair_injective
      (fundamentalHom D) (complementHom D C) hcomm hk hj)
  change P.prime ^ 4 ≤ Nat.card
    (GaloisField P.prime P.exponent × ExtensionField P)
  rw [Nat.card_prod, GaloisField.card P.prime P.exponent (Nat.ne_of_gt P.exponent_pos),
    card_extensionField, Parameters.q, ← pow_mul, ← pow_add]
  exact pow_le_pow_right' P.prime_prime.one_lt.le (by have := P.exponent_pos; omega)

theorem triality_defining_center_impossible {P : Parameters}
    (hr : Odd P.prime) (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)
    (hk : Function.Injective (fundamentalHom D))
    (hj : Function.Injective (complementHom D C))
    (hcomm : ∀ a b, Commute (fundamentalHom D a) (complementHom D C b))
    (iso : (G ⧸ center G) ≃* Carrier P)
    (hc : IsPGroup P.prime (center G)) (hG : IsQuasithin G) : False := by
  apply not_quasithin_triality_cover hr D C hk hj hcomm iso _ hG
  obtain ⟨k, hk⟩ := hc.exists_card_eq
  rw [hk]
  exact hr.pow

end CFSG.Quasithin.ChapterA.Section02.OddLie.DefiningKernel
