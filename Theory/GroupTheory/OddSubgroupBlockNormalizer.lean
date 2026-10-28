module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# An odd subgroup prevents exchange of commuting factors

Suppose distinct Q-conjugates of X commute, the center of X is a two-group,
and an odd nontrivial subgroup D of X normalizes the two-group Q. An element
of Q moving X would commute with every element of D: its commutator has
both odd and two-power order. That puts D in the two-group center of X,
a contradiction. Hence Q normalizes X.

Source application: the actual A₅ block orbit in Aschbacher--Smith15.2.23,
printed p.1115, refs/quasithin.pdf.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

theorem normalizes_of_odd_subgroup_and_commuting_conjugates
    (X Q D : Subgroup G) (hQ : IsPGroup 2 Q) (hD : Odd (Nat.card D)) (hd : D ≠ ⊥)
    (hDX : D ≤ X) (hDQ : D ≤ normalizer (Q : Set G))
    (hZ : IsPGroup 2 (center X))
    (hc : ∀ q ∈ Q, X ≠ X.map (MulAut.conj q).toMonoidHom →
      ⁅X, X.map (MulAut.conj q).toMonoidHom⁆ = ⊥) :
    Q ≤ normalizer (X : Set G) := by
  intro q hq
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  have hc' := commutator_eq_bot_iff_le_centralizer.mp (hc q hq (Ne.symm hne))
  have hDcenter : D ≤ centralizer (X : Set G) := by
    intro d hdD
    have hdpow : d ^ Nat.card D = 1 := congrArg D.subtype
      (pow_card_eq_one' (x := (⟨d,hdD⟩ : D)))
    let a := q * d⁻¹ * q⁻¹
    have ha : a ∈ X.map (MulAut.conj q).toMonoidHom :=
      mem_map_of_mem (MulAut.conj q).toMonoidHom (X.inv_mem (hDX hdD))
    have hcomm : Commute d a := (hc' (hDX hdD) a ha).symm
    have hp : (d*a) ^ Nat.card D = 1 := by
      rw [hcomm.mul_pow,hdpow]
      have hh : a ^ Nat.card D = 1 := by
        change ((MulAut.conj q) d⁻¹) ^ Nat.card D = 1
        rw [←map_pow,inv_pow,hdpow,inv_one,map_one]
      rw [hh,one_mul]
    have hmem : d*a ∈ Q := by
      change d * (q * d⁻¹ * q⁻¹) ∈ Q
      rw [←mul_assoc,←mul_assoc]
      exact Q.mul_mem ((mem_normalizer_iff.mp (hDQ hdD) q).mp hq) (Q.inv_mem hq)
    have hone : d*a=1 := by
      have hh : (⟨d*a,hmem⟩ : Q) = 1 := by
        apply (hQ.powEquiv hD.coprime_two_left).injective
        change (⟨d*a,hmem⟩ : Q) ^ Nat.card D = 1 ^ Nat.card D
        apply Subtype.ext
        change (d*a) ^ Nat.card D = 1 ^ Nat.card D
        simpa only [one_pow] using hp
      exact congrArg Q.subtype hh
    have he : d = q * d * q⁻¹ := by
      have hh := eq_inv_of_mul_eq_one_left hone
      simpa only [a,mul_inv_rev,inv_inv,mul_assoc] using hh
    have hdY : d ∈ X.map (MulAut.conj q).toMonoidHom :=
      he ▸ mem_map_of_mem (MulAut.conj q).toMonoidHom (hDX hdD)
    exact (le_centralizer_iff.mp hc') hdY
  apply hd
  apply eq_bot_iff.mpr
  intro d hdD
  let z : center X := ⟨⟨d,hDX hdD⟩,by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (hDcenter hdD x x.property)⟩
  have hz : z ^ Nat.card D = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg D.subtype (pow_card_eq_one' (x := (⟨d,hdD⟩ : D)))
  have hz1 : z = 1 := (hZ.powEquiv hD.coprime_two_left).injective
    (by change z ^ Nat.card D = 1 ^ Nat.card D; simpa only [one_pow] using hz)
  exact congrArg (fun z : center X => ((z : X) : G)) hz1
end Subgroup
