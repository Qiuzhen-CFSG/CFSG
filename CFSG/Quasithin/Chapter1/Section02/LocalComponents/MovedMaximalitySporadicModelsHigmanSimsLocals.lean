module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySporadicModelsJankoTwo
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeNormalizerThreePart

/-!
# Component uniqueness in the three Higman--Sims local normalizers

The involution local has a solvable two-group kernel and symmetric-five
quotient. The other two locals act on elementary abelian groups of order
at most eight, with two-group centralizers. Their images have orders dividing
168. Two distinct components would force two prime factors outside two and
three; neither quotient has enough such factors.

These are the local rows used by the full-Sylow overgroup calculation in
Aschbacher--Smith A.3.12(18), printed pp.47--48, and the moved-component
embedding restriction 1.2.8(1), printed p.506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality

private theorem unique_of_card_dvd {H : Type*} [Group H] [Finite H]
    (n m p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hc : Nat.card H ∣ 2^n * 3^m * p) : SylowOvergroupComponentUnique H := by
  intro S P _ B C hB hC
  by_contra hn
  obtain ⟨r,s,hr,hs,hr2,hr3,hs2,hs3,hd,_⟩ := hB.exists_prime_pair_of_ne hC hn
  have hd := hd.trans (P.card_subgroup_dvd_card.trans hc)
  have key (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
      (hd : r ∣ 2^n * 3^m * p) : r = p := by
    rcases hr.dvd_mul.mp hd with hd | hd
    · rcases hr.dvd_mul.mp hd with hd | hd
      · exact (hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
          (hr.dvd_of_dvd_pow hd))).elim
      · exact (hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
          (hr.dvd_of_dvd_pow hd))).elim
    · exact (Nat.prime_dvd_prime_iff_eq hr hp).mp hd
  have hrp := key r hr hr2 hr3 ((dvd_mul_right r s).trans hd)
  have hsp := key s hs hs2 hs3 ((dvd_mul_left s r).trans hd)
  rw [hrp,hsp] at hd
  have hdpp : p * p ∣ p * (2^n * 3^m) := by
    simpa only [Nat.mul_comm] using hd
  have hd : p ∣ 2^n * 3^m := (Nat.mul_dvd_mul_iff_left hp.pos).mp hdpp
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd))

open Sporadic.LeechRelated.HS.EvenLocalCandidates

/-- Every subgroup of the symmetric five-letter carrier has at most one component. -/
private theorem symmetric_five_unique : SylowOvergroupComponentUnique (Equiv.Perm (Fin 5)) := by
  apply unique_of_card_dvd 3 1 5 (by decide) (by decide) (by decide)
  rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  norm_num

/-- The actual HS involution local has unique components in its Sylow overgroups. -/
theorem higman_sims_central_local_unique : SylowOvergroupComponentUnique (localGroup 0) := by
  let f := CentralNormalizerThreePart.PairQuotient.fiveHom
  let : Group.IsSolvable f.ker := by
    rw [show f = CentralNormalizerThreePart.PairQuotient.fiveHom from rfl,
      CentralNormalizerThreePart.PairQuotient.fiveHom_kernel]
    let := CentralInvolutionCore.core_isPGroup.isNilpotent
    infer_instance
  exact SylowOvergroupComponentUnique.of_surjective f
    CentralNormalizerThreePart.PairQuotient.fiveHom_surjective symmetric_five_unique

private theorem small_elementary_aut_card {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hE : Nat.card E ≤ 8) : Nat.card (MulAut E) ∣ 168 := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hle : n ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hE
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn]
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

/-- The other two actual HS elementary normalizers have the same uniqueness property. -/
theorem higman_sims_large_local_unique (i : Fin 3) (hi : i ≠ 0) :
    SylowOvergroupComponentUnique (localGroup i) := by
  let _ := elementary_isElementaryAbelian i
  let f := (elementary i).normalizerMonoidHom
  have hk : IsPGroup 2 f.ker := by
    rw [normalizerMonoidHom_ker]
    exact (large_elementary_centralizer_isPGroup i hi).of_equiv
      (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (elementary i : Set Sporadic.LeechRelated.HS.Carrier))).symm
  let g := f.rangeRestrict
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable f.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    let _ := hk.isNilpotent
    infer_instance
  apply SylowOvergroupComponentUnique.of_surjective g f.rangeRestrict_surjective
  exact unique_of_card_dvd 3 1 7 (by decide) (by decide) (by decide)
    (f.range.card_subgroup_dvd_card.trans (small_elementary_aut_card (elementary_card_le_eight i)))

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
