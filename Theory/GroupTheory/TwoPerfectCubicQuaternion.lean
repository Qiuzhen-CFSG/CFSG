module

public import Theory.GroupAction.SupercriticalTwoPerfect
public import Theory.GroupTheory.PGroup.UniqueInvolutionAutomorphisms
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupAction.QuotientConjugation
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Factors
public import Theory.GroupTheory.TwoPerfectOddSupplement
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Cubic two-perfect extensions with a unique core involution

The two-core is cyclic or generalized quaternion. Except for Q₈ its
automorphism group is a two-group, so two-perfectness makes the core
central. The cubic quotient then makes the whole group abelian, a
contradiction. Thus the core is Q₈. A genuine order-three element supplements
it and acts nontrivially; quaternion–cubic recognition identifies the whole
group with SL₂(3), retaining its actual two-core.

Source: the small-linear actor step in Aschbacher–Smith 13.3.14(d),
printed p.892. Unique involution will be supplied by the determinant-one
matrix calculation rather than by an assumed actor model.
-/

public section
open Subgroup

namespace Subgroup

variable {A : Type*} [Group A] [Finite A]

private theorem core_ne_bot_precludes_two_aut
    (hA : IsPPerfect 2 A) (hthree : Nat.card (A ⧸ pCore 2 A) = 3)
    (hne : pCore 2 A ≠ ⊥) : ¬ IsPGroup 2 (MulAut (pCore 2 A)) := by
  intro haut
  let f : A →* MulAut (pCore 2 A) := MulAut.conjNormal
  have hf := hA.hom_eq_one_of_isPGroup haut f
  have hcenter : pCore 2 A ≤ center A := by
    intro q hq
    apply mem_center_iff.mpr
    intro a
    have hh := congrArg (fun z : A →* MulAut (pCore 2 A) => (z a ⟨q, hq⟩ : A)) hf
    change a * q * a⁻¹ = q at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let : IsCyclic (A ⧸ pCore 2 A) := isCyclic_of_prime_card hthree
  let : IsMulCommutative A := (QuotientGroup.mk' (pCore 2 A)).isMulCommutative_of_isCyclic_of_ker_le_center
    (by simpa only [QuotientGroup.ker_mk'] using hcenter)
  let : CommGroup A := IsMulCommutative.instCommGroup
  exact hne (by simpa only [map_id] using hA.twoCore_map_eq_bot_of_commutative (MonoidHom.id A))

theorem twoCore_quaternion_of_cubic_quotient
    (hA : IsPPerfect 2 A) (hthree : Nat.card (A ⧸ pCore 2 A) = 3)
    (hne : pCore 2 A ≠ ⊥)
    (hu : ∀ x y : pCore 2 A, orderOf x = 2 → orderOf y = 2 → x = y) :
    Nonempty ((pCore 2 A) ≃* QuaternionGroup 2) := by
  have hQ : IsPGroup 2 (pCore 2 A) := pCore_isPGroup
  let : Nontrivial (pCore 2 A) := (pCore 2 A).nontrivial_iff_ne_bot.mpr hne
  obtain ⟨w, hw⟩ := exists_ne (1 : pCore 2 A)
  have hz : orderOf (w ^ (orderOf w / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos w).ne' (hQ.dvd_orderOf hw)
  let z := w ^ (orderOf w / 2)
  have huniq : ∃! z : pCore 2 A, orderOf z = 2 := ⟨z, hz, fun y hy => hu y z hy hz⟩
  have hnot := core_ne_bot_precludes_two_aut hA hthree hne
  rcases hQ.isCyclic_or_quaternion_of_unique_involution huniq with hc | ⟨n, hn, ⟨e⟩⟩
  · let : IsCyclic (pCore 2 A) := hc
    exact (hnot hQ.mulAut_of_isCyclic_two).elim
  · by_cases he : n = 3
    · subst n
      exact ⟨e⟩
    · apply False.elim
      apply hnot
      have hn' : 2 < 2 ^ (n - 2) := by
        have hh : 2 ^ 2 ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by decide) (by omega)
        norm_num at hh ⊢
        omega
      exact (QuaternionGroup.isPGroup_mulAut_of_two_lt hn' (hQ.of_equiv e)).of_equiv
        (MulAut.congr e).symm

theorem binaryTetrahedral_of_cubic_quotient
    (hA : IsPPerfect 2 A) (hthree : Nat.card (A ⧸ pCore 2 A) = 3)
    (hne : pCore 2 A ≠ ⊥)
    (hu : ∀ x y : pCore 2 A, orderOf x = 2 → orderOf y = 2 → x = y) :
    Nonempty (A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      Nonempty ((pCore 2 A) ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := twoCore_quaternion_of_cubic_quotient hA hthree hne hu
  have hc : Nat.card (pCore 2 A) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    norm_num [QuaternionGroup.card]
  have hAcard : Nat.card A = 24 := by
    have hh := (pCore 2 A).card_mul_index
    change Nat.card (pCore 2 A) * Nat.card (A ⧸ pCore 2 A) = Nat.card A at hh
    rw [hc, hthree] at hh
    exact hh.symm
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (hAcard ▸ (by decide))
  have hxc : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hd : Disjoint (pCore 2 A) (zpowers x) :=
    disjoint_of_coprime_natCard (by rw [hc, hxc]; decide)
  have hg : pCore 2 A ⊔ zpowers x = ⊤ := by
    apply eq_top_of_card_eq
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ le_normalizer_of_normal hd,
      hc, hxc, hAcard]
  let a : MulAut (pCore 2 A) := MulAut.conjNormal x
  have ha : a ≠ 1 := by
    intro haz
    have hxcentral : x ∈ centralizer (pCore 2 A : Set A) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      exact haz
    have hz : ⁅pCore 2 A, zpowers x⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr hxcentral)
    exact hne ((commutator_two_core_eq_of_odd_supplement (zpowers x) hA
      (hxc ▸ (by decide)) hg).symm.trans hz)
  obtain ⟨⟨j⟩, _⟩ := quaternion_cubic_extension_recognition (pCore 2 A) ⟨e⟩
    x hx a (fun q => MulAut.conjNormal_apply x q) ha
  exact ⟨⟨(topEquiv.symm.trans (MulEquiv.subgroupCongr hg).symm).trans j⟩, ⟨e⟩⟩

end Subgroup
