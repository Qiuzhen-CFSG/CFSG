module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# Sylow-fixed conjugators with elementary abelian displacement

An involution fixed by a Sylow two-subgroup has an odd orbit. In a commutative
group the product over that orbit is fixed by the whole acting group and has
the same image under any homomorphism constant on the orbit.

Apply this to conjugation on an elementary abelian subgroup A. If the
conjugates of v differ from v by elements of U, the orbit product b centralizes
the acting subgroup, while z = v / b belongs to U and induces precisely the
same conjugation as v. Both b and z still have square one.

This elementary odd-index argument supplies the short-group action step in
Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7, printed p.246.
It avoids applying the quasisimple-only Lemma 16.1.6 to a short group.
-/

public section

open scoped BigOperators
open Subgroup
namespace Theory.GroupAction

variable {G A B : Type*} [Group G] [Finite G] [CommGroup A] [CommGroup B]
  [MulDistribMulAction G A]

/-- Multiplying the odd orbit of a Sylow-fixed involution gives a fixed lift
of its image under every homomorphism constant on that orbit. -/
theorem exists_fixed_lift_of_sylow_fixed (S : Sylow 2 G) (a : A)
    (ha : a ^ 2 = 1) (hS : ∀ s ∈ S, s • a = a)
    (f : A →* B) (hf : ∀ g : G, f (g • a) = f a) :
    ∃ b : A, (∀ g : G, g • b = b) ∧ f b = f a := by
  classical
  let O := MulAction.orbit G a
  let : Finite O := Finite.of_equiv (G ⧸ MulAction.stabilizer G a)
    (MulAction.orbitEquivQuotientStabilizer G a).symm
  let : Fintype O := Fintype.ofFinite O
  let b : A := ∏ x : O, (x : A)
  have hodd : Odd (Fintype.card O) := by
    have hle : (S : Subgroup G) ≤ MulAction.stabilizer G a := hS
    have hn : ¬ 2 ∣ (MulAction.stabilizer G a).index := fun hd =>
      S.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le hle))
    have hc : Fintype.card O = (MulAction.stabilizer G a).index := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G a)
    rw [hc]
    exact Nat.odd_iff.mpr (by omega)
  refine ⟨b, ?_, ?_⟩
  · intro g
    change (MulDistribMulAction.toMonoidHom A g) (∏ x : O, (x : A)) = _
    rw [map_prod (MulDistribMulAction.toMonoidHom A g)]
    exact Fintype.prod_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
  · have he : f b = (f a) ^ Fintype.card O := by
      change f (∏ x : O, (x : A)) = _
      rw [map_prod]
      calc
        (∏ x : O, f (x : A)) = ∏ _x : O, f a := by
          apply Finset.prod_congr rfl
          intro x _
          obtain ⟨g, hg⟩ := x.property
          rw [← hg, hf]
        _ = _ := by simp
    rw [he]
    obtain ⟨n, hn⟩ := hodd
    rw [hn, pow_add, pow_mul, ← map_pow, ha, map_one, one_pow, one_mul, pow_one]

end Theory.GroupAction

open scoped IsMulCommutative commutatorElement

namespace Theory.GroupAction

variable {K : Type*} [Group K] [Finite K]

/-- Odd-orbit averaging in an elementary abelian subgroup turns an external
conjugator into an internal one in the supplied displacement subgroup. -/
theorem exists_conjugating_element_of_elementary_displacement
    (L U A : Subgroup K) [IsElementaryAbelian 2 A]
    (hLA : L ≤ normalizer (A : Set K))
    (S : Sylow 2 L) (v : A)
    (hfix : ∀ s : L, s ∈ S → (s : K) * (v : K) * (s : K)⁻¹ = (v : K))
    (hcomm : ∀ l : L, ⁅(l : K), (v : K)⁆ ∈ U) :
    ∃ z ∈ U, z ^ 2 = 1 ∧
      ∀ l : L, z * (l : K) * z⁻¹ = (v : K) * (l : K) * (v : K)⁻¹ := by
  let ρ : L →* MulAut A := A.normalizerMonoidHom.comp (inclusion hLA)
  let : MulDistribMulAction L A := MulDistribMulAction.compHom A ρ
  let f := QuotientGroup.mk' (U.subgroupOf A)
  have hf (l : L) : f (l • v) = f v := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ((l : K) * (v : K) * (l : K)⁻¹) / (v : K) ∈ U
    simpa only [div_eq_mul_inv, commutatorElement_def] using hcomm l
  obtain ⟨b, hb, he⟩ := exists_fixed_lift_of_sylow_fixed S v
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) v)
    (fun s hs => Subtype.ext (hfix s hs)) f hf
  let z : A := v / b
  have hz : (z : K) ∈ U := QuotientGroup.eq_iff_div_mem (N := U.subgroupOf A) |>.mp he.symm
  refine ⟨z, hz, elemPow_eq_one_of_isElementaryAbelian (z : K) z.property, ?_⟩
  intro l
  have hc : (l : K) * (b : K) = (b : K) * (l : K) :=
    mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hb l))
  have hcb : (b : K)⁻¹ * (l : K) * (b : K) = (l : K) := by
    rw [mul_assoc, hc, inv_mul_cancel_left]
  change ((v : K) / (b : K)) * (l : K) * ((v : K) / (b : K))⁻¹ = _
  calc
    _ = (v : K) * ((b : K)⁻¹ * (l : K) * (b : K)) * (v : K)⁻¹ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc]
    _ = _ := by rw [hcb]

end Theory.GroupAction
