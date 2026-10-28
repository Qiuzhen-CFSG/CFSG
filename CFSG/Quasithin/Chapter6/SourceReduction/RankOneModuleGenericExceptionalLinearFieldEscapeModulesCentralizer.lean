module
public import Theory.GroupTheory.NormalizerQuotientInner
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.PSL3Four.ThreeRank
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The three-prime quotient centralizer in 5.1.16(1)

Pass to the quotient by O₂(K). The quotient-action kernel commutes with
the actual K-image. Since PSL₃(4) has trivial center and three-rank at
least two, rank addition forces the kernel to have three-rank zero in
the strongly quasithin normalizer. Cauchy's theorem then gives order
prime to three. The quotient action and its kernel are the literal
normalizer action, without ambient normality of K.

Only the normalizer's odd-rank bound and the supplied PSL₃(4) quotient
are needed; parity and the choice of cubic Cartan play no role.
Source: Aschbacher--Smith, 5.1.16(1), printed p.639.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {G : Type*} [Group G] [Finite G]
/-- The literal quotient-action centralizer has order prime to three. -/
public theorem quotientAction_kernel_three_prime (K : Subgroup G)
    (hN : IsStronglyQuasithin (normalizer (K : Set G)))
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    Nat.Coprime 3 (Nat.card (normalizerQuotientAction K (pCore 2 K)).ker) := by
  let N := normalizer (K : Set G)
  let a := normalizerQuotientAction K (pCore 2 K)
  let C : Subgroup G := a.ker.map N.subtype
  have hCN : C ≤ N := map_subtype_le _
  have hcomm : ⁅C, K⁆ ≤ K.pCoreIn 2 := by
    apply commutator_le.mpr
    intro c hc k hk
    obtain ⟨x, hx, rfl⟩ := hc
    have he : a x = 1 := hx
    have hf := congrArg (fun f : MulAut (K ⧸ pCore 2 K) =>
      f (QuotientGroup.mk' (pCore 2 K) ⟨k, hk⟩)) he
    simp only [a, normalizerQuotientAction, MonoidHom.comp_apply,
      quotientAut_apply_mk, MulAut.one_apply] at hf
    have hh : K.normalizerMonoidHom x ⟨k,hk⟩ / ⟨k,hk⟩ ∈ pCore 2 K :=
      QuotientGroup.eq_iff_div_mem.mp hf
    have hh' := mem_map_of_mem K.subtype hh
    change (((K.normalizerMonoidHom x) ⟨k, hk⟩ : K) : G) / k ∈ K.pCoreIn 2 at hh'
    rw [normalizerMonoidHom_apply_apply_coe, div_eq_mul_inv] at hh'
    exact hh'
  have hr := ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 3) C K hCN
    ((commutator_mono (map_subtype_le _) le_rfl).trans hcomm)
    (by
      obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
      let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
      rw [Nat.card_congr (centerCongr e).toEquiv,
        Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)]
      simp)
  have hupper : primeRank 3 (C ⊔ K : Subgroup G) ≤ 2 :=
    (primeRank_mono 3 (sup_le hCN K.le_normalizer)).trans
      (hN 3 Nat.prime_three (by decide))
  have hK : 2 ≤ primeRank 3 K := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let := Fintype.ofFinite Matrix.PSL3Four.F
    let eF : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq
      (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        hF, Matrix.PSL3Four.card_F])
    have hq : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
      rw [primeRank_congr 3 (e.trans (Atlas.fieldEquivPSL 3 eF))]
      exact Matrix.PSL3Four.ThreeRank.three_rank_ge_two
    exact hq.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
  have hzero : primeRank 3 C = 0 := by omega
  have hker : primeRank 3 a.ker = 0 := by
    rwa [primeRank_congr 3 (a.ker.equivMapOfInjective N.subtype N.subtype_injective)]
  exact Nat.prime_three.coprime_iff_not_dvd.mpr (PrimeRank.eq_zero_iff_not_dvd_card.mp hker)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
