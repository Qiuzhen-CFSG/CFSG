module

public import Stellmacher.SectionTwo.QuotientAction
public import Stellmacher.SectionTwo.VSubgroupElementaryAbelian
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# The Baumann image fixes the Thompson fixed space

In the Section 2 quotient action, any subgroup B centralizing Ω₁(Z(J(S)))
fixes every vector fixed by the image of J(S). This applies to the source's
Baumann subgroup B=S∩C_G(Ω₁(Z(J(S)))).

A quotient-fixed vector commutes with J(S). Its cyclic subgroup is
elementary abelian and lies in S, so the maximal-elementary centralizer
public theorem places it in Ω₁(Z(J(S))). Thus B centralizes that vector, which
means its image fixes the vector under the exact named quotient action.

This supplies the fixed-space premise for normalizing the selected
rank-one factors in the final paragraph of Stellmacher (2.2),
Journal of Algebra 190 (1997), p.20, in
`refs/latex/stellmacher-n-group.tex`. No classification hypothesis is used.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem baumann_image_fixes_thompson_fixedPoints
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] (q : G →* barG)
    (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (B : Subgroup G)
    (hB : B ≤ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)) :
    letI := quotientConjugationAction S q hq hker
    B.map q ≤ fixingSubgroup barG
      (FixedPoints.subgroup ((elementaryAbelianMaxJ (S : Subgroup G)).map q)
        (vSubgroup S) : Set (vSubgroup S)) := by
  let := quotientConjugationAction S q hq hker
  obtain ⟨hVcore, hVelem⟩ := vSubgroup_le_twoCore_and_elementaryAbelian h S
  let : IsElementaryAbelian 2 (vSubgroup S) := hVelem
  have hVS : vSubgroup S ≤ (S : Subgroup G) :=
    hVcore.trans (fitting_pCore_le_sylow S)
  rintro b ⟨b₀, hb₀, rfl⟩
  rw [mem_fixingSubgroup_iff]
  intro v hv
  have hvC : (v : G) ∈ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hfix := (FixedPoints.mem_subgroup
      (M := (elementaryAbelianMaxJ (S : Subgroup G)).map q) (a := v)).mp hv
      ⟨q j, Subgroup.mem_map_of_mem q hj⟩
    change q j • v = v at hfix
    have heq := congrArg Subtype.val hfix
    rw [quotientConjugationAction_smul_coe S q hq hker] at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  let : IsElementaryAbelian 2 (Subgroup.zpowers (v : G)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (v : G) v.property)
  have hvOmega : (v : G) ∈
      omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) :=
    elementary_centralizer_maxJ_le_omegaCenter (S : Subgroup G)
      (Subgroup.zpowers (v : G))
      (Subgroup.zpowers_le.mpr (hVS v.property))
      (Subgroup.zpowers_le.mpr hvC) (Subgroup.mem_zpowers (v : G))
  apply Subtype.ext
  rw [quotientConjugationAction_smul_coe S q hq hker]
  have hcomm := Subgroup.mem_centralizer_iff.mp (hB hb₀) v hvOmega
  rw [← hcomm, mul_inv_cancel_right]

end Stellmacher.SectionTwo
