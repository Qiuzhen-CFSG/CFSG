module

public import Theory.GroupTheory.PGroup.CriticalSubgroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Maximal characteristic subgroups of exponent p with central commutators

Choose a maximal characteristic subgroup X of exponent dividing p with
[P,X] central in X. If a characteristic subgroup K of exponent dividing p
centralizes X but is not contained in X, its image modulo Z(X) has nontrivial
intersection with the center of P/Z(X). The preimage inside K gives a
characteristic enlargement of X satisfying the same conditions.

This is the maximality step of Aschbacher, *Finite Group Theory*, (23.6)
and (24.9), applied directly to subgroups of exponent dividing p. The
order-p centralizer condition still requires the odd-prime second-center
argument; it is not asserted here.
-/

open Subgroup
open scoped commutatorElement

namespace SupercriticalConstruction

private def candidate {P : Type*} [Group P] (p : ℕ) (X : Subgroup P) : Prop :=
  X.Characteristic ∧ ⁅X, (⊤ : Subgroup P)⁆ ≤ (center X).map X.subtype ∧
    ∀ x : P, x ∈ X → x ^ p = 1

private theorem candidate_sup {P : Type*} [Group P] {p : ℕ}
    {X R : Subgroup P} (hX : candidate p X) [R.Characteristic]
    (hRpow : ∀ r : P, r ∈ R → r ^ p = 1)
    (hRX : R ≤ centralizer (X : Set P))
    (hRcomm : ⁅R, (⊤ : Subgroup P)⁆ ≤ (center X).map X.subtype) :
    candidate p (X ⊔ R) := by
  let : X.Characteristic := hX.1
  let Z := (center X).map X.subtype
  have hZX : Z ≤ X := map_subtype_le _
  have hZCX : Z ≤ centralizer (X : Set P) := by
    dsimp [Z]
    rw [map_center_subtype_eq_inf_centralizer]
    exact inf_le_right
  have hZCR : Z ≤ centralizer (R : Set P) := by
    exact le_centralizer_iff.mp (hRX.trans (centralizer_le hZX))
  have hZsup : Z ≤ (center ↥(X ⊔ R)).map (X ⊔ R).subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    refine le_inf (hZX.trans le_sup_left) ?_
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp hZCX) (le_centralizer_iff.mp hZCR)
  refine ⟨inferInstance, ?_, ?_⟩
  · apply Subgroup.commutator_le.mpr
    intro a ha g _
    obtain ⟨x, hx, r, hr, rfl⟩ := mem_sup_of_normal_left.mp ha
    apply hZsup
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact Z.mul_mem
      ((inferInstance : Z.Normal).conj_mem _
        (hRcomm (commutator_mem_commutator hr (mem_top g))) x)
      (hX.2.1 (commutator_mem_commutator hx (mem_top g)))
  · intro a ha
    obtain ⟨x, hx, r, hr, rfl⟩ := mem_sup_of_normal_left.mp ha
    have hxr : Commute x r := hRX hr x hx
    rw [hxr.mul_pow, hX.2.2 x hx, hRpow r hr, one_mul]

end SupercriticalConstruction

namespace IsPGroup

/-- A finite p-group has a characteristic subgroup with central ambient
commutators and exponent dividing p that absorbs every characteristic
exponent-p subgroup of its centralizer. -/
public theorem exists_characteristic_exponent_subgroup_saturated
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) :
    ∃ X : Subgroup P, X.Characteristic ∧
      ⁅X, (⊤ : Subgroup P)⁆ ≤ (center X).map X.subtype ∧
      Monoid.exponent X ∣ p ∧
      ∀ K : Subgroup P, K.Characteristic → Monoid.exponent K ∣ p →
        K ≤ centralizer (X : Set P) → K ≤ X := by
  classical
  open SupercriticalConstruction in
  have hbot : candidate p (⊥ : Subgroup P) := by
    refine ⟨inferInstance, ?_, ?_⟩
    · simp
    · intro x hx
      rw [mem_bot.mp hx, one_pow]
  obtain ⟨X, _, hmax⟩ := Finite.exists_le_maximal
    (p := SupercriticalConstruction.candidate p) hbot
  let : X.Characteristic := hmax.1.1
  refine ⟨X, hmax.1.1, hmax.1.2.1, ?_, ?_⟩
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    exact Subtype.ext (hmax.1.2.2 x x.property)
  · intro K hK hKpow hKC
    let : K.Characteristic := hK
    by_contra hnot
    let Z := (center X).map X.subtype
    let : Z.Characteristic := inferInstance
    let q : P →* P ⧸ Z := QuotientGroup.mk' Z
    let Kbar := K.map q
    let : Kbar.Normal := QuotientGroup.map_normal Z K
    let : Fact (IsPGroup p (P ⧸ Z)) := ⟨hP.to_quotient Z⟩
    have hZX : Z ≤ X := map_subtype_le _
    have hKbar : Nontrivial Kbar := by
      obtain ⟨k, hkK, hkX⟩ := SetLike.not_le_iff_exists.mp hnot
      have hkbar : q k ∈ Kbar := mem_map_of_mem q hkK
      refine ⟨⟨⟨q k, hkbar⟩, 1, ?_⟩⟩
      intro he
      exact hkX (hZX ((QuotientGroup.eq_one_iff (N := Z) k).mp
        (congrArg Subtype.val he)))
    let := hKbar
    obtain ⟨t, ht, htcenter⟩ := exists_nontrivial_center_mem_normal (p := p) Kbar
    obtain ⟨k, hkK, hkt⟩ := t.property
    let R := K ⊓ (center (P ⧸ Z)).comap q
    let : ((center (P ⧸ Z)).comap q).Characteristic :=
      Characteristic.comap_quotient_mk inferInstance
    let : R.Characteristic := inferInstance
    have hkR : k ∈ R := by
      refine ⟨hkK, ?_⟩
      change q k ∈ center (P ⧸ Z)
      rw [hkt]
      exact htcenter
    have hkX : k ∉ X := by
      intro hk
      have hkZ : k ∈ Z := by
        dsimp [Z]
        rw [map_center_subtype_eq_inf_centralizer]
        exact ⟨hk, hKC hkK⟩
      apply ht
      exact Subtype.ext (hkt.symm.trans ((QuotientGroup.eq_one_iff (N := Z) k).mpr hkZ))
    have hRpow (r : P) (hr : r ∈ R) : r ^ p = 1 :=
      congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hKpow
        (⟨r, hr.1⟩ : K))
    have hRcomm : ⁅R, (⊤ : Subgroup P)⁆ ≤ Z := by
      apply Subgroup.commutator_le.mpr
      intro r hr g _
      apply (QuotientGroup.eq_one_iff (N := Z) _).mp
      change q ⁅r, g⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((mem_center_iff.mp hr.2 (q g)).symm)
    have hgood := SupercriticalConstruction.candidate_sup hmax.1 hRpow
      ((inf_le_left : R ≤ K).trans hKC) hRcomm
    exact hkX ((hmax.2 hgood le_sup_left) ((show R ≤ X ⊔ R from le_sup_right) hkR))

end IsPGroup
