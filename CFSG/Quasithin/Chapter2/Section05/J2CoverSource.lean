module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local.SourceLifting
public import Theory.GroupTheory.DoubleCoverCentralizer.MarkedInversion
public import Theory.SpecificGroups.ExceptionalOuterDisplacements.J2

/-!
# The original J₂-cover contradiction in 2.5.19

The original normalizing involution acts outerly on the marked J₂ quotient.
Its quotient displacement lifts to an inverted element of order four whose
quotient image still has order two. The original covering center is ⟨i⟩,
so the square is i. Conjugating by the inverse of that element sends t to ti
inside the original ambient group.

Source: Aschbacher–Smith 2.5.19, case (β), printed pp.561–562. This replaces
only the quoted quaternion-root calculation, retaining the original L, t, i,
central quotient and ambient inclusion. No multiplier or Conway cover is used.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.J2CoverSource
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers
variable {G : Type*} [Group G] [Finite G]

/-- The source outer action supplies an actual element of the original L
whose square is i and whose inverse conjugates t to ti. -/
theorem exists_conjugator_of_outer_double_cover
    (L : Subgroup G) [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.J2.Carrier)
    (t i : G) (htN : t ∈ normalizer (L : Set G)) (ht : orderOf t = 2) (hi : orderOf i = 2)
    (hcenter : (center L).map L.subtype = zpowers i)
    (hout : ¬ ∃ s : Sporadic.LeechRelated.J2.Carrier,
      MulAut.centralQuotientAction e (L.normalizerMonoidHom ⟨t, htN⟩) = MulAut.conj s) :
    ∃ y : L, orderOf y = 4 ∧
      orderOf (QuotientGroup.mk' (center L) y) = 2 ∧
      (y : G) ^ 2 = i ∧ (MulAut.conj ((y : G)⁻¹)) t = t * i := by
  classical
  have hZ : Nat.card (center L) = 2 := by
    rw [← card_map_of_injective L.subtype_injective, hcenter, Nat.card_zpowers, hi]
  let α : MulAut L := L.normalizerMonoidHom ⟨t, htN⟩
  have htN2 : (⟨t, htN⟩ : normalizer (L : Set G)) ^ 2 = 1 := by
    apply Subtype.ext
    exact ht ▸ pow_orderOf_eq_one t
  have hα2 : α ^ 2 = 1 := by
    change (L.normalizerMonoidHom ⟨t, htN⟩) ^ 2 = 1
    rw [← map_pow, htN2, map_one]
  have hα1 : α ≠ 1 := by
    intro h
    apply hout
    refine ⟨1, ?_⟩
    change MulAut.centralQuotientAction e α = _
    simp [h]
  have hα : orderOf α = 2 := orderOf_eq_prime hα2 hα1
  have hβ : orderOf (MulAut.centralQuotientAction e α) = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) α).trans hα
  have hd := Theory.SpecificGroups.ExceptionalOuterDisplacements.J2.outer_displacement
    (MulAut.centralQuotientAction e α) hβ hout
  obtain ⟨y, hy4, hyinv, hyq, _⟩ := inverts_four_with_involution_image e hZ
    (J2Local.nonTwoCentral_involution_lifting e hZ) α hα hd
  have hysq : y ^ 2 ∈ center L := by
    apply (QuotientGroup.eq_one_iff (y ^ 2)).mp
    change QuotientGroup.mk' (center L) (y ^ 2) = 1
    rw [map_pow, ← hyq, pow_orderOf_eq_one]
  have hysq_mem : (y : G) ^ 2 ∈ zpowers i := by
    rw [← hcenter]
    exact mem_map_of_mem L.subtype hysq
  have hysq_ne : (y : G) ^ 2 ≠ 1 := by
    intro h
    have hy2 : y ^ 2 = 1 := Subtype.ext h
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    norm_num [hy4] at hdvd
  have hysq_eq : (y : G) ^ 2 = i := by
    rw [mem_zpowers_iff_mem_range_orderOf, hi] at hysq_mem
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hysq_mem
    have hn2 : n < 2 := Finset.mem_range.mp hn
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · exact (hysq_ne (by simpa only [pow_zero] using he.symm)).elim
    · simpa only [pow_one] using he.symm
  have hrel : t * (y : G) * t⁻¹ = (y : G)⁻¹ := by
    exact congrArg (fun x : L => (x : G)) hyinv
  refine ⟨y, hy4, hyq, hysq_eq, ?_⟩
  calc
    (MulAut.conj ((y : G)⁻¹)) t = (y : G)⁻¹ * t * (y : G) := by
      simp only [MulAut.conj_apply, inv_inv]
    _ = (t * (y : G) * t⁻¹) * t * (y : G) := by rw [hrel]
    _ = t * (y : G) ^ 2 := by
      simp only [pow_two]
      group
    _ = t * i := by rw [hysq_eq]

/-- The conjugacy conclusion is in the original ambient group. -/
theorem isConj_mul_center_of_outer_double_cover
    (L : Subgroup G) [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.J2.Carrier)
    (t i : G) (htN : t ∈ normalizer (L : Set G)) (ht : orderOf t = 2) (hi : orderOf i = 2)
    (hcenter : (center L).map L.subtype = zpowers i)
    (hout : ¬ ∃ s : Sporadic.LeechRelated.J2.Carrier,
      MulAut.centralQuotientAction e (L.normalizerMonoidHom ⟨t, htN⟩) = MulAut.conj s) :
    IsConj t (t * i) := by
  obtain ⟨y, _, _, _, hy⟩ :=
    exists_conjugator_of_outer_double_cover L e t i htN ht hi hcenter hout
  exact isConj_iff.mpr ⟨(y : G)⁻¹, hy⟩

/-- Applying the preceding source nonfusion contradicts the J₂ double-cover branch. -/
theorem false_of_outer_double_cover_of_not_isConj
    (L : Subgroup G) [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* Sporadic.LeechRelated.J2.Carrier)
    (t i : G) (htN : t ∈ normalizer (L : Set G)) (ht : orderOf t = 2) (hi : orderOf i = 2)
    (hcenter : (center L).map L.subtype = zpowers i)
    (hout : ¬ ∃ s : Sporadic.LeechRelated.J2.Carrier,
      MulAut.centralQuotientAction e (L.normalizerMonoidHom ⟨t, htN⟩) = MulAut.conj s)
    (hn : ¬ IsConj t (t * i)) : False :=
  hn (isConj_mul_center_of_outer_double_cover L e t i htN ht hi hcenter hout)

end CFSG.Quasithin.Chapter2.Section05.J2CoverSource
