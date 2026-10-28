module
public import Stellmacher.SectionTwo.QuotientOffenders
public import Stellmacher.SectionTwo.BaumannFixedPoints

/-!
# Relative Baumann inputs on the original Section Two module

Let Q contain the original normal closure V of the central involutions of S.
The maximal-order elementary subgroups of Q give quotient offenders on this
same V. Any B centralizing Ω₁(Z(J(Q))) fixes the Thompson fixed space of V.
Q need not be the original Sylow subgroup, and V is not redefined from Q.

The relative maximal-elementary cardinal bound gives the offender inequality.
For the fixed-space assertion, a fixed vector centralizes J(Q); its elementary
cyclic subgroup lies in Q, so the elementary-centralizer theorem places it
in Ω₁(Z(J(Q))). B therefore fixes it. Both conclusions preserve the named
original quotient-conjugation action exactly.

Source: the offender and Baumann fixed-space arguments of Stellmacher (2.2),
Journal of Algebra 190 (1997), p20, applied to the original V and Q=O₂(C)
in (4.6), p26. This separates the subgroup transport from factor recognition.
-/

namespace Stellmacher.SectionTwo
universe u

/-- Relative maximal-elementary and Baumann data act on the unchanged original V. -/
public theorem relative_baumann_action_inputs
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] (q : G →* barG)
    (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (Q B : Subgroup G) (hVQ : vSubgroup S ≤ Q)
    (hB : B ≤ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G)) :
    letI := quotientConjugationAction S q hq hker
    (∀ A ∈ elementaryAbelianMaxSubgroups Q,
      SectionOne.oneA (V := vSubgroup S) (Q.map q) (A.map q)) ∧
    B.map q ≤ fixingSubgroup barG
      (FixedPoints.subgroup ((elementaryAbelianMaxJ Q).map q)
        (vSubgroup S) : Set (vSubgroup S)) := by
  let := quotientConjugationAction S q hq hker
  let : Finite barG := Finite.of_surjective q hq
  let : IsElementaryAbelian 2 (vSubgroup S) :=
    (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let : (vSubgroup S).Normal := Subgroup.normalClosure_normal
  constructor
  · intro A hA
    have hbound := maxElementary_card_le_fixed_mul_image Q (vSubgroup S) A hVQ hA q hker
    rw [← quotientConjugationAction_fixedPoints_card S q hq hker A] at hbound
    refine ⟨Subgroup.map_mono hA.1, hA.2.1.map q, ?_⟩
    unfold SectionOne.m
    have hpos : 0 < (Nat.card (FixedPoints.subgroup (A.map q) (vSubgroup S)) : ℚ) *
        (Nat.card (A.map q) : ℚ) := by
      exact_mod_cast Nat.mul_pos Nat.card_pos Nat.card_pos
    apply (div_le_one hpos).mpr
    exact_mod_cast hbound
  · rintro b ⟨b₀, hb₀, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hvC : (v : G) ∈ Subgroup.centralizer (elementaryAbelianMaxJ Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hfix := (FixedPoints.mem_subgroup
        (M := (elementaryAbelianMaxJ Q).map q) (a := v)).mp hv
        ⟨q j, Subgroup.mem_map_of_mem q hj⟩
      change q j • v = v at hfix
      have heq := congrArg Subtype.val hfix
      rw [quotientConjugationAction_smul_coe S q hq hker] at heq
      exact mul_inv_eq_iff_eq_mul.mp heq
    let : IsElementaryAbelian 2 (Subgroup.zpowers (v : G)) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) (v : G) v.property)
    have hvOmega : (v : G) ∈ omegaOneCenterAmbient (elementaryAbelianMaxJ Q) :=
      elementary_centralizer_maxJ_le_omegaCenter Q (Subgroup.zpowers (v : G))
        (Subgroup.zpowers_le.mpr (hVQ v.property))
        (Subgroup.zpowers_le.mpr hvC) (Subgroup.mem_zpowers (v : G))
    apply Subtype.ext
    rw [quotientConjugationAction_smul_coe S q hq hker]
    have hcomm := Subgroup.mem_centralizer_iff.mp (hB hb₀) v hvOmega
    rw [← hcomm, mul_inv_cancel_right]

end Stellmacher.SectionTwo
