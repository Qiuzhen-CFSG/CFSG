module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.ModelFacts
public import CFSG.Quasithin.Chapter16.Section03.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# The HS order comparisons in 16.3.4

The full HS carrier has two-part 512. The automorphism groups of A₆ and A₈
have two-parts 32 and 128 respectively. Actual group equivalences transport
these orders to the embedded groups; no central quotient is substituted.

Source: Aschbacher–Smith, proof of 16.3.4, printed p.1178; GLS3, Table 5.3m.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup ClassificationModels

private theorem hs_sylow_card {K : Type*} [Group K] [Finite K]
    (e : K ≃* SporadicName.hs.Carrier) (S : Sylow 2 K) : Nat.card S = 512 := by
  have hk : Nat.card K = 44352000 := (Nat.card_congr e.toEquiv).trans
    Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier
  rw [S.card_eq_multiplicity, hk]
  rw [show 44352000 = 2 ^ 9 * 86625 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 86625)]
  rfl

/-- The strict Sylow order gap for the A₆ component of HS. -/
theorem hs_sylowOrderGap_a6 {G : Type*} [Group G] [Finite G]
    {L K : Subgroup G} (eK : K ≃* SporadicName.hs.Carrier)
    (eL : L ≃* alternatingGroup (Fin 6)) : SylowOrderGap L K := by
  intro A S
  have hc : Nat.card (MulAut L) = 1440 :=
    (Nat.card_congr (MulAut.congr eL).toEquiv).trans AlternatingSix.ShadowLocal.card_aut
  have ha : Nat.card A = 32 := by
    rw [A.card_eq_multiplicity, hc]
    rw [show 1440 = 2 ^ 5 * 45 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
    rfl
  rw [ha, hs_sylow_card eK S]
  decide

/-- The strict Sylow order gap for the A₈ component of HS. -/
theorem hs_sylowOrderGap_a8 {G : Type*} [Group G] [Finite G]
    {L K : Subgroup G} (eK : K ≃* SporadicName.hs.Carrier)
    (eL : L ≃* alternatingGroup (Fin 8)) : SylowOrderGap L K := by
  intro A S
  have hc : Nat.card (MulAut L) = 40320 := by
    rw [Nat.card_congr (MulAut.congr eL).toEquiv,
      Nat.card_congr (GLS3.Chapter5.theorem_5_2_1_a (by decide) (by decide)
        (Ω := Fin 8)).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have ha : Nat.card A = 128 := by
    rw [A.card_eq_multiplicity, hc]
    rw [show 40320 = 2 ^ 7 * 315 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]
    rfl
  rw [ha, hs_sylow_card eK S]
  decide

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
