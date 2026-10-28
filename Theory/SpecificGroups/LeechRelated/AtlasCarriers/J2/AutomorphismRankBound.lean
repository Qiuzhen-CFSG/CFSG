module
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms.Full
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.Eight

/-!
# A sufficient automorphism two-rank bound for Hall--Janko FF modules

The actual permutation extension is the full automorphism group and has a
Sylow two-subgroup of order 256. The checked order-eight carrier element has
a conjugate in that Sylow subgroup. An elementary subgroup of order greater
than 64 would have index one or two, forcing every element to have fourth
power one. This proves the bound six needed by the B.4 FF degree reduction.
No sharper elementary-subgroup classification is required.

Source application: GM02 Proposition 5.1, J2 paragraph, and
Aschbacher--Smith B.4.2 and K.4, printed pp.86 and 457--460.
-/

public section
open Subgroup Theory.GroupTheory

private theorem elementary_card_le_sixty_four {P : Type*} [Group P] [Finite P]
    (hc : Nat.card P = 256) (x : P) (hx : x ^ 4 ≠ 1)
    (A : Subgroup P) [IsElementaryAbelian 2 A] : Nat.card A ≤ 64 := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hle : 2 ^ n ≤ 2 ^ 8 := by
    simpa only [hn, hc, show 2 ^ 8 = 256 from by decide] using
      Nat.card_le_card_of_injective A.subtype A.subtype_injective
  have hn8 : n ≤ 8 := (pow_le_pow_iff_right₀ (by decide : 1 < 2)).mp hle
  by_contra! hbig
  have hn7 : 7 ≤ n := by
    by_contra! h
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show n ≤ 6 by omega)
    rw [← hn] at hh
    omega
  have hncase : n = 7 ∨ n = 8 := by omega
  have hindex : A.index = 1 ∨ A.index = 2 := by
    have hh := A.card_mul_index
    rcases hncase with rfl | rfl <;> rw [hn, hc] at hh <;> norm_num only [Nat.reducePow] at hh <;> omega
  have hmem : x ^ 2 ∈ A := by
    rcases hindex with h | h
    · rw [Subgroup.index_eq_one.mp h]
      trivial
    · exact A.sq_mem_of_index_two h x
  have hpow : (⟨x ^ 2,hmem⟩ : A) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) _
  apply hx
  have hh : (x ^ 2) ^ 2 = 1 := congrArg (fun a : A => (a : P)) hpow
  simpa only [← pow_mul] using hh

namespace Sporadic.LeechRelated.J2
open ExceptionalParabolics RecognitionGeometry.VertexExtension

/-- The literal full automorphism group has two-rank at most six. -/
theorem automorphism_primeRank_le_six : primeRank 2 (MulAut Carrier) ≤ 6 := by
  let S := SecondParabolic.outerSylow FirstParabolic.card_l₁
  have hx : orderOf (intoExtension eight) = 2 ^ 3 := by
    rw [orderOf_injective intoExtension SecondParabolic.intoExtension_injective, orderOf_eight]
    decide
  obtain ⟨y, hy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow hx
  have hyo : orderOf y = 8 := by
    rw [← orderOf_injective (S : Subgroup Extension).subtype (S : Subgroup Extension).subtype_injective]
    change orderOf (y : Extension) = 8
    obtain ⟨c,hc⟩ := isConj_iff.mp hy
    rw [← hc]
    change orderOf (MulAut.conj c (intoExtension eight)) = 8
    rw [MulEquiv.orderOf_eq, hx]
    decide
  have hy4 : y ^ 4 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hyo] at hd
    norm_num at hd
  rw [← primeRank_equiv 2 extensionEquivAut, S.primeRank_eq]
  apply (primeRank_le_iff_elementary_card_le S).mpr
  intro A hA
  let := hA
  exact elementary_card_le_sixty_four (SecondParabolic.card_outerSylow _) y hy4 A

end Sporadic.LeechRelated.J2
