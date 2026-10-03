module

public import Stellmacher.SectionTwo.QuotientAction
public import Stellmacher.SectionTwo.VSubgroupElementaryAbelian
public import Stellmacher.MaxElementaryOffender

/-!
# Maximal elementary subgroups give quotient offenders

In the Section 2 setup, each maximal-order elementary abelian subgroup A
of the Sylow subgroup maps into the Section 1 offender family for the
faithful quotient action on V. Consequently the image of the elementary
Thompson subgroup J(S) lies in the action-defined subgroup J(V,q(S)).

The normal subgroup V is elementary abelian and lies in the 2-core, hence
in S. The maximal elementary subgroup cardinal bound, transported through
the exact named quotient-conjugation action's fixed-point lemma, gives
m(q(A)) ≤ 1. Containment and elementary abelianity transport by q. Taking
the defining supremum then gives the assertion for J(S).

These are the reductions in the first paragraph of Stellmacher (2.2),
Journal of Algebra 190 (1997), p.20, in
`refs/latex/stellmacher-n-group.tex`. They are independent of the subsequent
classification arguments (1.6) and (1.7).
-/

namespace Stellmacher.SectionTwo
universe u
variable {G : Type u} [Group G] [Finite G]
  (h : Hypotheses G) (S : Sylow 2 G)
  {barG : Type u} [Group barG] (q : G →* barG)
  (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)

include h

public theorem maxElementary_map_mem_oneA (A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G)) :
    letI := quotientConjugationAction S q hq hker
    SectionOne.oneA (V := vSubgroup S) ((S : Subgroup G).map q) (A.map q) := by
  let := quotientConjugationAction S q hq hker
  let : Finite barG := Finite.of_surjective q hq
  obtain ⟨hVcore, hVelem⟩ := vSubgroup_le_twoCore_and_elementaryAbelian h S
  let : IsElementaryAbelian 2 (vSubgroup S) := hVelem
  let : (vSubgroup S).Normal := Subgroup.normalClosure_normal
  have hVS : vSubgroup S ≤ (S : Subgroup G) :=
    hVcore.trans (fitting_pCore_le_sylow S)
  have hbound := maxElementary_card_le_fixed_mul_image
    (S : Subgroup G) (vSubgroup S) A hVS hA q hker
  rw [← quotientConjugationAction_fixedPoints_card S q hq hker A] at hbound
  refine ⟨Subgroup.map_mono hA.1, hA.2.1.map q, ?_⟩
  unfold SectionOne.m
  have hpos : 0 < (Nat.card (FixedPoints.subgroup (A.map q) (vSubgroup S)) : ℚ) *
      (Nat.card (A.map q) : ℚ) := by
    exact_mod_cast Nat.mul_pos Nat.card_pos Nat.card_pos
  apply (div_le_one hpos).mpr
  exact_mod_cast hbound

public theorem elementaryAbelianMaxJ_map_le_oneJ :
    letI := quotientConjugationAction S q hq hker
    (elementaryAbelianMaxJ (S : Subgroup G)).map q ≤
      SectionOne.oneJ (V := vSubgroup S) ((S : Subgroup G).map q) := by
  let := quotientConjugationAction S q hq hker
  rw [Subgroup.map_le_iff_le_comap]
  apply sSup_le
  intro A hA
  apply Subgroup.map_le_iff_le_comap.mp
  exact le_sSup (maxElementary_map_mem_oneA h S q hq hker A hA)

end Stellmacher.SectionTwo
