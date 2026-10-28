module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Omega
public import Theory.Frattini.PGroup

/-!
# The nilpotent radical action on its omega quotient

For A.3.6(4), the actual group Ω₁(Oₚ(K))/Φ(Ω₁(Oₚ(K))) is elementary
abelian of order p². In the extraspecial case Ω₁(Oₚ(K)) is the whole core;
in the homocyclic case only its first omega layer is used.

The p-core acts trivially on this quotient, and all other prime cores
centralize it. Thus the Fitting subgroup lies in the kernel of the actual
conjugation action, which descends to K/F*(K). These statements do not assert
that the descended action is nontrivial or faithful. Those require the
C-component and common A.3.6 assertions, beyond the displayed core shapes.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6(4)
and its proof, pp.43–45; the actions used in 1.3.3 and 1.3.8, pp.509, 513.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.RadicalActions.Nilpotent
variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

private theorem extraspecial_frattini [IsExtraspecial p K] : frattini K = center K := by
  have hK : IsPGroup p K := IsExtraspecial.isPGroup p K
  let : Fact (IsPGroup p K) := ⟨hK⟩
  let : IsElementaryAbelian p (K ⧸ center K) := IsExtraspecial.quotient_elementary_abelian p K
  let : Fact (IsPGroup p (K ⧸ center K)) := ⟨hK.to_quotient _⟩
  have hle : frattini K ≤ center K := by
    have h := frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective (center K))
    rw [frattini_eq_bot_of_isElementaryAbelian (R := K ⧸ center K) (p := p)] at h
    simpa using h
  have hne : frattini K ≠ ⊥ := by
    intro hbot
    let : IsElementaryAbelian p K :=
      (frattini_eq_bot_iff_isElementaryAbelian (p := p)).mp hbot
    let : Nontrivial (K ⧸ center K) := IsExtraspecial.quotient_nontrivial p K
    have hs : Subsingleton (K ⧸ center K) :=
      QuotientGroup.subsingleton_iff.mpr center_eq_top
    exact not_subsingleton (K ⧸ center K) hs
  have hd : Nat.card (frattini K) ∣ p := by
    rw [← IsExtraspecial.center_order_p p K]
    exact card_dvd_of_le hle
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with hc | hc
  · exact (hne (card_eq_one.mp hc)).elim
  · apply eq_of_le_of_card_ge hle
    rw [hc, IsExtraspecial.center_order_p p K]

private theorem shape_frattini (h : XiOddQuotient p K) :
    IsElementaryAbelian p (K ⧸ frattini K) ∧ Nat.card (K ⧸ frattini K) = p ^ 2 := by
  rcases h with ⟨he, hc⟩ | ⟨he, hc, _⟩
  · let := he
    let : Fact (IsPGroup p K) := ⟨IsElementaryAbelian.isPGroup p K⟩
    refine ⟨isElementaryAbelian_quotient_frattini (p := p), ?_⟩
    rw [Nat.card_congr (frattiniQuotientEquivOfIsElementaryAbelian (R := K) (p := p)).toEquiv]
    exact hc
  · let := he
    let : Fact (IsPGroup p K) := ⟨IsExtraspecial.isPGroup p K⟩
    refine ⟨isElementaryAbelian_quotient_frattini (p := p), ?_⟩
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
      (extraspecial_frattini (K := K) (p := p))).toEquiv]
    have hcard := card_eq_card_quotient_mul_card_subgroup (center K)
    rw [hc, IsExtraspecial.center_order_p p K] at hcard
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
      (hcard.symm.trans (by ring : p ^ 3 = p ^ 2 * p))

omit [Finite K] [Fact p.Prime] in
theorem omega_le_core : omegaCore p K ≤ pCore p K := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

omit [Finite K] [Fact p.Prime] in
theorem omega_isPGroup : IsPGroup p (omegaCore p K) :=
  (pCore_isPGroup (p := p) (G := K)).to_le omega_le_core

theorem frattini_shape (h : A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) :
    IsElementaryAbelian p (omegaCore p K ⧸ frattini (omegaCore p K)) ∧
      Nat.card (omegaCore p K ⧸ frattini (omegaCore p K)) = p ^ 2 := by
  have hs := (RadicalStructure.core_omega (Or.inr h) hd).2
  exact shape_frattini (hs.of_mulEquiv
    ((omega (pCore p K) (p := p) 1).equivMapOfInjective
      (pCore p K).subtype (pCore p K).subtype_injective))

private theorem core_le_action_ker
    (hs : IsMulCommutative (pCore p K) ∨ ∀ x : pCore p K, x ^ p = 1) :
    pCore p K ≤ (omegaFrattiniAction p K).ker := by
  let : Fact (IsPGroup p (omegaCore p K)) := ⟨omega_isPGroup⟩
  let : IsElementaryAbelian p (omegaCore p K ⧸ frattini (omegaCore p K)) :=
    isElementaryAbelian_quotient_frattini (p := p)
  intro g hg
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini (omegaCore p K)) v
  change quotientAut (frattini (omegaCore p K)) (omegaCoreAction p K g)
    (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
  rw [quotientAut_apply_mk]
  rcases hs with ha | he
  · let := ha
    have hfix : omegaCoreAction p K g x = x := by
      apply Subtype.ext
      rw [omegaCoreAction_apply]
      have hcomm : g * (x : K) = (x : K) * g :=
        congrArg Subtype.val (mul_comm (⟨g, hg⟩ : pCore p K)
          ⟨x, omega_le_core x.property⟩)
      rw [hcomm, mul_inv_cancel_right]
    rw [hfix]
  · have hW : omegaCore p K = pCore p K := by
      unfold omegaCore
      rw [RadicalStructure.omega_top he, ← MonoidHom.range_eq_map, range_subtype]
    let w : omegaCore p K := ⟨g, hW.symm ▸ hg⟩
    have hinner : omegaCoreAction p K g x = w * x * w⁻¹ := by
      apply Subtype.ext
      rfl
    rw [hinner, map_mul, map_mul, map_inv,
      mul_comm (QuotientGroup.mk' (frattini (omegaCore p K)) w)
        (QuotientGroup.mk' (frattini (omegaCore p K)) x), mul_inv_cancel_right]

omit [Finite K] in
private theorem other_core_le_action_ker {q : ℕ} [Fact q.Prime] (hne : q ≠ p) :
    pCore q K ≤ (omegaFrattiniAction p K).ker := by
  intro a ha
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini (omegaCore p K)) v
  change quotientAut (frattini (omegaCore p K)) (omegaCoreAction p K a)
    (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
  rw [quotientAut_apply_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  rw [omegaCoreAction_apply,
    pCore_commute_of_ne q p hne a ha x (omega_le_core x.property),
    mul_inv_cancel_right]

/-- Every primary factor of the Fitting subgroup acts trivially on the omega quotient. -/
theorem fitting_le_action_ker (h : A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) :
    fittingSubgroup K ≤ (omegaFrattiniAction p K).ker := by
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun q => ?_
  let : Fact q.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors q.val.property⟩
  by_cases heq : q.val.val = p
  · rw [heq]
    exact core_le_action_ker (RadicalStructure.core_shape (Or.inr h) hd)
  · exact other_core_le_action_ker heq

/-- The actual action descended through the generalized Fitting subgroup. -/
noncomputable def quotientAction (h : A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) :
    (K ⧸ generalizedFitting K) →*
      MulAut (omegaCore p K ⧸ frattini (omegaCore p K)) :=
  QuotientGroup.lift (generalizedFitting K) (omegaFrattiniAction p K)
    (h.1.symm ▸ fitting_le_action_ker h hd)

theorem quotientAction_apply_mk (h : A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) (g : K) :
    quotientAction h hd (QuotientGroup.mk' (generalizedFitting K) g) =
      omegaFrattiniAction p K g := rfl

end CFSG.Quasithin.Chapter1.RadicalActions.Nilpotent
