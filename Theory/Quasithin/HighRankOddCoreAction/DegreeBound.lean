module
public import Theory.Quasithin.HighRankOddCoreAction.RankBound
public import Theory.Representation.ElementaryTwoFixedDegree

/-!
# The actual supercritical Frattini quotient has degree at most four

When the ambient two-rank is at least three, A.1.28 supplies an elementary
eight. Its action on the chosen supercritical Frattini quotient is faithful,
since the actual action kernel has odd order. Coprime fixed lifting bounds
each involution fixed space by dimension two, so the elementary-eight degree
bound applies to the same Frattini quotient.

Source: Aschbacher--Smith A.1.28, printed p.26. The consumer is the full
M₂₂-cover comparison in 4.2.13, printed p.612.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.Quasithin
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The original supercritical Frattini space has dimension at most four. -/
theorem supercritical_frattini_finrank_le_four
    (hp : Odd p)
    (hlocal : ∀ a : G, orderOf a = 2 → primeRank p (centralizer ({a} : Set G)) ≤ 2)
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup p Q) (hQrank : 2 < primeRank p Q)
    (hthree : 3 ≤ primeRank 2 G) (X : Subgroup Q) (hX : IsSupercriticalPSubgroup p X) :
    letI : Fact (IsPGroup p X) := ⟨hQ.to_subgroup X⟩
    letI : IsElementaryAbelian p (X ⧸ frattini X) := isElementaryAbelian_quotient_frattini
    Module.finrank (ZMod p) (Additive (X ⧸ frattini X)) ≤ 4 := by
  classical
  have hp2 : p ≠ 2 := fun he => by subst p; exact (by decide : ¬ Odd 2) hp
  have hrank := two_rank_le_three_and_center_oddCore_of_large_normal_p_subgroup hp hlocal Q hQ hQrank
  have hr : primeRank 2 G = 3 := Nat.le_antisymm hrank.1 hthree
  obtain ⟨A,hA,hAc⟩ := exists_elementaryAbelian_card_primeRank (G := G) (p := 2)
  let := hA
  have hA8 : Nat.card A = 8 := by simpa only [hr,show 2 ^ 3 = 8 from rfl] using hAc
  let : X.Characteristic := hX.characteristic
  let : Fact (IsPGroup p X) := ⟨hQ.to_subgroup X⟩
  let : IsElementaryAbelian p (X ⧸ frattini X) := isElementaryAbelian_quotient_frattini
  let f : G →* MulAut (X ⧸ frattini X) :=
    ((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp MulAut.conjNormal
  have hodd : Odd (Nat.card f.ker) :=
    odd_card_supercritical_frattini_kernel hp hlocal Q hQ hQrank X hX
  let fA : A →* MulAut (X ⧸ frattini X) := f.comp A.subtype
  have hfA : Function.Injective fA := injective_comp_subtype_of_coprime_ker f
    hodd.coprime_two_left A (IsElementaryAbelian.isPGroup 2 A)
  let : MulDistribMulAction A (X ⧸ frattini X) :=
    MulDistribMulAction.compHom (X ⧸ frattini X) fA
  let ρ : Representation (ZMod p) A (Additive (X ⧸ frattini X)) :=
    Representation.ofElementaryAbelianAction
  have hρ : Function.Injective ρ := by
    intro a b he
    apply hfA
    ext x
    exact congrArg (fun r : Module.End (ZMod p) (Additive (X ⧸ frattini X)) => r (Additive.ofMul x)) he
  have hpow (a : A) : (a : G)^2=1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) a)
  have ho (a : A) (ha : a ≠ 1) : orderOf (a : G)=2 :=
    orderOf_eq_prime (hpow a) (fun he => ha (Subtype.ext he))
  have hfix (a : A) (ha : a ≠ 1) :
      Module.finrank (ZMod p) (Module.End.eigenspace (ρ a) 1) ≤ 2 := by
    let α : MulAut X := MulAut.characteristic X (MulAut.conjNormal (a : G))
    have hα : α ^ 2 = 1 := by
      change (((MulAut.characteristic X).comp (MulAut.conjNormal : G →* MulAut Q)) (a : G)) ^ 2 = 1
      rw [← map_pow, hpow, map_one]
    have hr : primeRank p α.fixedSubgroup ≤ 2 :=
      (primeRank_fixed_characteristic_conjugation_le p Q X (a : G)).trans (hlocal a (ho a ha))
    have hc := MulAut.card_fixed_frattini_le_prime_sq (hQ.to_subgroup X) hp2
      hX.pow_eq_one hX.derived_le_center α hα hr
    exact finrank_eigenspace_one_le_of_fixed_card fA a hc
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro he
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp he
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left (Fact.out : p.Prime).ne_one)
  exact Representation.ElementaryTwoFixedRank.finrank_le_four_of_card_eight ρ hρ htwo hfix hA8
end Theory.Quasithin
