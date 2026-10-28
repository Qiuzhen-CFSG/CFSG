module

public import Theory.Mathieu.M12.A5Fixer.Automorphisms.OuterIndex
public import Theory.Mathieu.M12.A5Fixer.Automorphisms.FiveFixer.Inner

/-!
# Reducing the full five-element fixer to an outer involution

The inner centralizer is cyclic of exponent ten and is fixed pointwise by
any automorphism fixing the marked five-element. An outer involution fixing
that element therefore commutes with all the inner automorphisms in its fixer.
The proved outer-index bound shows that every other fixer element is an inner
one or its product with this involution. Both kinds have tenth power one.

The second theorem needs only an outer involution whose fixed subgroup has
order divisible by five. Cauchy's theorem and Sylow conjugacy supply the marked
witness without prescribing a particular generator of its fixed five-subgroup.

The outer witness remains an explicit model obligation. Neither theorem here
asserts unconditional `FiveFixerExponent`; constructing the outer witness is
still required. Source context: Aschbacher–Smith 16.1.5(4), 16.1.7(3f), and
16.3.5, combined manuscript of 1 March 2004, printed pp.1171–1173 and 1178–1179.
-/

public section
namespace Sporadic.Mathieu.M12A5Fixer.Automorphisms
open Subgroup

/-- An outer involution fixing the marked element completes the exponent bound
for the full abstract automorphism fixer. -/
theorem fiveFixerExponent_of_outer_involution
    (b : MulAut M12) (hb : b fiveElement = fiveElement)
    (hb2 : b ^ 2 = 1) (hout : b ∉ MulAut.innerSubgroup M12) :
    FiveFixerExponent := by
  have hi : (MulAut.innerSubgroup M12).index = 2 := by
    have hlo := (MulAut.innerSubgroup M12).one_lt_index_of_ne_top
      (fun h => hout (h ▸ mem_top b))
    have hhi : (MulAut.innerSubgroup M12).index ≤ 2 := outerIndexBound
    omega
  have inner_pow (a : MulAut M12) (ha : a fiveElement = fiveElement)
      (hinner : a ∈ MulAut.innerSubgroup M12) : a ^ 10 = 1 := by
    obtain ⟨g, rfl⟩ := hinner
    have hg : Commute g fiveElement := by
      change g * fiveElement * g⁻¹ = fiveElement at ha
      exact mul_inv_eq_iff_eq_mul.mp ha
    rw [← map_pow, fiveCentralizer_pow_ten hg, map_one]
  intro a ha
  by_cases hainner : a ∈ MulAut.innerSubgroup M12
  · exact inner_pow a ha hainner
  have habinner : a * b ∈ MulAut.innerSubgroup M12 :=
    (mul_mem_iff_of_index_two hi).mpr (iff_of_false hainner hout)
  obtain ⟨g, hg⟩ := habinner
  have hgab : MulAut.conj g = a * b := hg
  have hgfive : Commute g fiveElement := by
    have h : (MulAut.conj g) fiveElement = fiveElement := by
      rw [hgab, MulAut.mul_apply, hb, ha]
    change g * fiveElement * g⁻¹ = fiveElement at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hcomm : Commute (MulAut.conj g) b := by
    apply MulEquiv.ext
    intro x
    change g * b x * g⁻¹ = b (g * x * g⁻¹)
    rw [map_mul, map_mul, map_inv, fiveCentralizer_fixed b hb hgfive]
  have haeq : a = MulAut.conj g * b := by
    rw [hgab, mul_assoc, ← pow_two, hb2, mul_one]
  rw [haeq, hcomm.mul_pow, ← map_pow, fiveCentralizer_pow_ten hgfive, map_one,
    one_mul, show (10 : ℕ) = 2 * 5 by decide, pow_mul, hb2, one_pow]

private noncomputable def markedFiveSylow (x : M12) (hx : orderOf x = 5) : Sylow 5 M12 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact Sylow.ofCard (zpowers x) (by rw [Nat.card_zpowers, hx, m12_order]; decide +kernel)

/-- The outer witness may fix any subgroup of order five: Sylow conjugacy
moves that subgroup onto the marked one before applying the exponent argument. -/
theorem fiveFixerExponent_of_outer_involution_fixed_card
    (b : MulAut M12) (hb2 : b ^ 2 = 1) (hout : b ∉ MulAut.innerSubgroup M12)
    (hfive : 5 ∣ Nat.card b.fixedSubgroup) : FiveFixerExponent := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := b.fixedSubgroup) 5 hfive
  have hx' : orderOf (x : M12) = 5 := (Subgroup.orderOf_coe x).trans hx
  let P := markedFiveSylow x hx'
  let Q := markedFiveSylow fiveElement fiveElement_order
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 P Q
  let e : MulAut M12 := MulAut.conj g
  let c : MulAut M12 := MulAut.congr e b
  have hmem : e.symm fiveElement ∈ zpowers (x : M12) := by
    have hm : fiveElement ∈ (g • P : Sylow 5 M12) := by
      rw [hg]
      exact mem_zpowers fiveElement
    change fiveElement ∈ (zpowers (x : M12)).map e.toMonoidHom at hm
    obtain ⟨y, hy, hey⟩ := hm
    have hye : y = e.symm fiveElement := (e.eq_symm_apply).mpr hey
    rwa [hye] at hy
  have hle : zpowers (x : M12) ≤ b.fixedSubgroup := zpowers_le.mpr x.property
  have hc : c fiveElement = fiveElement := by
    change e (b (e.symm fiveElement)) = fiveElement
    rw [(MulAut.mem_fixedSubgroup b _).mp (hle hmem), e.apply_symm_apply]
  have hc2 : c ^ 2 = 1 := by
    change (MulAut.congr e b) ^ 2 = 1
    rw [← map_pow, hb2, map_one]
  have hcout : c ∉ MulAut.innerSubgroup M12 := by
    intro h
    rw [← MulAut.map_innerSubgroup_congr e] at h
    obtain ⟨d, hd, he⟩ := h
    have hdb : d = b := (MulAut.congr e).injective he
    exact hout (hdb ▸ hd)
  exact fiveFixerExponent_of_outer_involution c hc hc2 hcout

end Sporadic.Mathieu.M12A5Fixer.Automorphisms
