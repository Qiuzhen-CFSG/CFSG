module
public import Theory.SpecificGroups.SymmetricFive.FiveNormalizerSuzuki
public import Theory.ElementaryAbelian.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Elementary two-subgroups in the index-five quotient models

In a five-normalizer in S₅, an elementary two-subgroup acts faithfully on
the normal cyclic subgroup of order five. Its image in the cyclic group
of automorphisms therefore has order at most two. Transport gives the
same bound for the concrete Sz(2). The order-ten dihedral case follows
from Lagrange and the power-of-two order of an elementary two-group.

These are the quotient-image bounds used with the opposite-vertex
geometry in Aschbacher–Smith 14.2.20(1).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem elementary_normalizer_card_le_two (P : Sylow 5 D)
    (E : Subgroup (normalizer ((P : Subgroup D) : Set D)))
    [IsElementaryAbelian 2 E] : Nat.card E ≤ 2 := by
  let f : E →* MulAut P := (P : Subgroup D).normalizerMonoidHom.comp E.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    have hxp : (x.val : D) ∈ (P : Subgroup D) := by
      have hh : x.val ∈ (P : Subgroup D).normalizerMonoidHom.ker := hx
      rwa [normalizerMonoidHom_ker, centralizer_eq P] at hh
    have h2 : orderOf (x.val : D) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (congrArg (fun y : E => (y.val : D))
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 E) x))
    have h5 : orderOf (x.val : D) ∣ 5 := by
      have hh := orderOf_dvd_natCard (⟨x.val, hxp⟩ : (P : Subgroup D))
      change orderOf (⟨x.val, hxp⟩ : (P : Subgroup D)) ∣ Nat.card (P : Subgroup D) at hh
      rwa [Subgroup.orderOf_mk, card_sylow P] at hh
    have he : (x.val : D) = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 5) h2 h5)
    exact Subtype.ext (Subtype.ext he)
  let : IsCyclic P := isCyclic_of_prime_card (card_sylow P)
  let a : MulAut P ≃* (ZMod 5)ˣ := by
    have e := IsCyclic.mulAutMulEquiv P
    rw [card_sylow P] at e
    exact e
  let : IsCyclic (MulAut P) := isCyclic_of_injective a.toMonoidHom a.injective
  let : IsCyclic E := isCyclic_of_injective f hf
  have hd := IsElementaryAbelian.exponent_dvd_p 2 E
  rw [IsCyclic.exponent_eq_card] at hd
  exact Nat.le_of_dvd (by decide) hd

theorem elementary_suzuki_zero_card_le_two
    (E : Subgroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    [IsElementaryAbelian 2 E] : Nat.card E ≤ 2 := by
  let P : Sylow 5 D := Classical.choice inferInstance
  obtain ⟨e⟩ := normalizer_equiv_suzuki P
  let : IsElementaryAbelian 2 (E.map e.symm.toMonoidHom) := IsElementaryAbelian.map _
  have h := elementary_normalizer_card_le_two P (E.map e.symm.toMonoidHom)
  rwa [card_map_of_injective e.symm.injective] at h

theorem elementary_dihedral_five_card_le_two
    (E : Subgroup (DihedralGroup 5)) [IsElementaryAbelian 2 E] : Nat.card E ≤ 2 := by
  have hd : Nat.card E ∣ 10 := by
    have hh := E.card_subgroup_dvd_card
    simpa only [Nat.card_eq_fintype_card, DihedralGroup.card] using hh
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 E)
  have hp : 2 ^ k ∣ 10 := by simpa [hk] using hd
  have hk_le : k ≤ 1 := by
    by_contra hn
    have hk2 : 2 ≤ k := by omega
    have hfour : 4 ∣ 2 ^ k := by
      have hpow := Nat.pow_dvd_pow 2 hk2
      norm_num at hpow
      exact hpow
    have : 4 ∣ 10 := dvd_trans hfour hp
    norm_num at this
  rw [hk]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk_le
end Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups
