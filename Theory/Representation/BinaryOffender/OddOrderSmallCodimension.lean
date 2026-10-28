module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.FixedQuotientKernel
public import Mathlib.Data.Fintype.Perm

/-!
# Odd-order elements moving at most two binary dimensions

In a faithful binary representation, an odd-order element with fixed codimension
at most two has order dividing three. Its action on the actual quotient by its
fixed space permutes at most four vectors, so its twenty-fourth power is trivial
there. The kernel on that quotient is a two-group. Oddness therefore makes the
same power trivial in the original group, and removes the factor eight.

This supplies the small linear-group step of GLS, *The Classification of the
Finite Simple Groups*, vol. 2, Theorem 26.24 Step 2;
`refs/KGroup/GLS2/ChapterG.tex`, lines 1225–1230.
-/

public section

open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem representation_pow_twentyFour_of_finrank_le_two
    (ρ : Representation (ZMod 2) G V) (hd : Module.finrank (ZMod 2) V ≤ 2)
    (x : G) : ρ (x ^ 24) = 1 := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype V := Fintype.ofFinite V
  let τ : G →* Equiv.Perm V :=
    { toFun := fun g =>
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
          (ρ.asGroupHom g)).toEquiv
      map_one' := by ext v; simp
      map_mul' := by intro g h; ext v; simp }
  have hcard : Fintype.card V ≤ 4 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2)]
    simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd)
  have hdiv : orderOf (τ x) ∣ 24 := by
    have h := orderOf_dvd_natCard (τ x)
    rw [Nat.card_eq_fintype_card, Fintype.card_perm] at h
    exact h.trans (Nat.factorial_dvd_factorial hcard)
  have hpow : τ (x ^ 24) = 1 := by
    rw [map_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp hdiv
  ext v
  exact congrArg (fun e : Equiv.Perm V => e v) hpow

/-- The only possible odd orders moving at most two binary dimensions divide three. -/
theorem orderOf_dvd_three_of_odd_fixedCodim_le_two
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (x : G) (hx : Odd (orderOf x)) (hd : fixedCodim ρ (zpowers x) ≤ 2) :
    orderOf x ∣ 3 := by
  let X := zpowers x
  let x' : X := ⟨x, mem_zpowers x⟩
  let σ := fixedQuotientRepresentation ρ X
  have hpow : σ (x' ^ 24) = 1 :=
    representation_pow_twentyFour_of_finrank_le_two σ hd x'
  have hmem : x' ^ 24 ∈ pCore 2 X :=
    fixedQuotient_ker_le_pCore ρ hf X (MonoidHom.mem_ker.mpr hpow)
  let b : pCore 2 X := ⟨x' ^ 24, hmem⟩
  have hxodd : Odd (orderOf x') := by simpa only [x', Subgroup.orderOf_mk] using hx
  have hbodd : Odd (orderOf b) := by
    simpa only [b, Subgroup.orderOf_mk] using
      hxodd.of_dvd_nat (orderOf_pow_dvd (x := x') 24)
  have hb : b = 1 := by
    by_contra hn
    exact hbodd.not_two_dvd_nat ((pCore_isPGroup (p := 2) (G := X)).dvd_orderOf hn)
  have hxpow : x ^ 24 = 1 := congrArg (fun z : pCore 2 X => ((z : X) : G)) hb
  have hdiv : orderOf x ∣ 2 ^ 3 * 3 := orderOf_dvd_iff_pow_eq_one.mpr hxpow
  exact (hx.coprime_two_right.pow_right 3).dvd_mul_left.mp hdiv


end Representation.BinaryOffender
