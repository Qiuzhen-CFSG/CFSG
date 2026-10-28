module

public import Theory.SpecificGroups.SL2.NormalMonolith
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.PPrimeCore

/-!
# The odd core and two-rank of odd-characteristic SL₂

The scalar minus identity has order two. Every nontrivial normal subgroup
contains it, so the odd core is trivial. Every matrix whose square is one
is one of the two scalars; elementary abelian two-subgroups therefore have
order at most two, and the scalar involution attains that bound.

These intrinsic matrix facts supply the model consequences in
Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.29(2),
printed p.27. They include the three-element field without any assertion
that SL₂(3) is perfect.
-/

open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F]
omit [Finite F] in
private theorem neg_one_ne_one_rank_two (hF : (2 : F) ≠ 0) :
    (-1 : SL(2,F)) ≠ 1 := by
  intro h
  have he := congrArg (fun g : SL(2,F) => g.val 0 0) h
  have he' : (-1 : F) = 1 := by simpa using he
  exact hF (by linear_combination -he')

omit [Finite F] in
/-- The scalar minus identity is an involution in odd characteristic. -/
public theorem orderOf_neg_one_eq_two (hF : (2 : F) ≠ 0) :
    orderOf (-1 : SL(2,F)) = 2 :=
  orderOf_eq_prime (by simp) (neg_one_ne_one_rank_two hF)

/-- SL₂ over a finite odd-characteristic field has trivial odd core. -/
public theorem pPrimeCore_two_eq_bot (hF : (2 : F) ≠ 0) :
    pPrimeCore 2 SL(2,F) = ⊥ := by
  apply eq_bot_of_neg_one_not_mem hF
  intro hn
  have hd := orderOf_dvd_natCard (pPrimeCore 2 SL(2,F)) hn
  rw [orderOf_neg_one_eq_two hF] at hd
  exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 2)).mp
    pPrimeCore_coprime_card hd

/-- SL₂ over a finite odd-characteristic field has two-rank one. -/
public theorem primeRank_two_eq_one (hF : (2 : F) ≠ 0) : primeRank 2 SL(2,F) = 1 := by
  classical
  have hne := neg_one_ne_one_rank_two hF
  apply le_antisymm
  · apply (primeRank_le_iff_elementary_card_le SL(2,F)).mpr
    intro A hA
    have hset : (A : Set SL(2,F)) ⊆ {1, -1} := by
      intro x hx
      have hs : x ^ 2 = 1 := congrArg Subtype.val
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p (⟨x,hx⟩ : A))
      have hdet : (toGL x).det = 1 := by apply Units.ext; exact x.property
      rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF
          (toGL x) (by rw [← map_pow, hs, map_one]) hdet with he | he
      · exact Or.inl (toGL_injective (by simpa using he))
      · exact Or.inr (Subtype.ext (congrArg Units.val he))
    have hb := Set.ncard_le_ncard hset
    rw [Set.ncard_pair (Ne.symm hne)] at hb
    have he : Nat.card A = (A : Set SL(2,F)).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr (Equiv.refl A)
    simpa only [he, pow_one] using hb
  · by_contra hb
    have hr : primeRank 2 SL(2,F) ≤ 0 := by omega
    let : IsElementaryAbelian 2 (zpowers (-1 : SL(2,F))) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (by simp)
    have hc := (primeRank_le_iff_elementary_card_le SL(2,F)).mp hr
      (zpowers (-1 : SL(2,F))) inferInstance
    rw [Nat.card_zpowers, orderOf_neg_one_eq_two hF] at hc
    norm_num at hc
end Matrix.SpecialLinearGroup

