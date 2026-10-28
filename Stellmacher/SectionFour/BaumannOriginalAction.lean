module
public import Stellmacher.SectionFour.BaumannFactorDecomposition

/-!
# The original quotient action in the critical-partner configuration

The actual native Sylow SP inside Pstar maps to the original S. Its original
module V and the literal Baumann normal closure L retain the rich raw factor
family inside the normal quotient image of E = O^2(Pstar) O_2(C).
The caller supplies the exact quotient map, kernel proof, and native Sylow;
the conclusion uses their exact quotientConjugationAction instance.

Compare native Sylows using their injective ambient images. The original V
containment supplies the normal-supplement action hypothesis; injective
Baumann transport identifies the literal subgroup B. The rich decomposition
then applies without replacing the original module or changing action data.

This is the source-family transport for the line and Hall arguments in
Stellmacher (4.6), journal p26; refs/latex/stellmacher-n-group.tex.
-/

open scoped Pointwise
namespace Stellmacher.SectionFour
universe u

public theorem baumann_original_action_data
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E)
    (SP : Sylow 2 Pstar) (hsec : SectionTwo.Hypotheses Pstar)
    (hSPmap : (SP : Subgroup Pstar).map Pstar.subtype = (S : Subgroup G))
    (hV : SectionTwo.vSubgroup SP =
      Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar))
    {X : Type u} [Group X] [Finite X] (q : Pstar →* X)
    (hq : Function.Surjective q) (hker : q.ker = SectionTwo.cSubgroup SP) :
    let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
    let L := Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)
    let _ := SectionTwo.quotientConjugationAction SP q hq hker
    SectionTwo.BaumannFactorActionData (SectionTwo.vSubgroup SP) L q
      ((E.subgroupOf Pstar).map q) := by
  obtain ⟨hEN, _, _, _, SP', Q, hSP'map, hQmap, hgen, _, _, hSN⟩ :=
    baumann_normal_supplement_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  let N := E.subgroupOf Pstar
  let _ : N.Normal := hEN
  let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
  let _ := SectionTwo.quotientConjugationAction SP q hq hker
  have hSP : (SP : Subgroup Pstar) = (SP' : Subgroup Pstar) := by
    apply Subgroup.map_injective Pstar.subtype_injective
    exact hSPmap.trans hSP'map.symm
  have hgen' : N ⊔ (SP : Subgroup Pstar) = ⊤ := by rw [hSP]; exact hgen
  have hSN' : (SP : Subgroup Pstar) ≤ Subgroup.normalizer
      (((Q : Subgroup N).map N.subtype : Subgroup Pstar) : Set Pstar) := by
    rw [hSP]
    exact hSN
  have hVQ : SectionTwo.vSubgroup SP ≤ (Q : Subgroup N).map N.subtype := by
    apply (Subgroup.map_le_map_iff_of_injective Pstar.subtype_injective).mp
    rw [hV, hQmap]
    exact original_v_le_c_core S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  let BN := (Q : Subgroup N).map N.subtype ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient
      (elementaryAbelianMaxJ ((Q : Subgroup N).map N.subtype)) : Set Pstar)
  have hBNmap : BN.map Pstar.subtype = B := by
    rw [baumann_map_injective Pstar.subtype Pstar.subtype_injective, hQmap]
  have hBP : B ≤ Pstar := by
    rw [← hBNmap]
    exact Subgroup.map_subtype_le _
  have hBsub : B.subgroupOf Pstar = BN := by
    apply Subgroup.map_injective Pstar.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hBP, hBNmap]
  have hdata := (SectionTwo.normal_supplement_baumann_action_decomposition
    hsec SP q hq hker N Q hgen' hSN' hVQ).1
  change SectionTwo.BaumannFactorActionData (SectionTwo.vSubgroup SP)
    (Subgroup.normalClosure (BN : Set Pstar)) q (N.map q) at hdata
  change SectionTwo.BaumannFactorActionData (SectionTwo.vSubgroup SP)
    (Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)) q (N.map q)
  rw [hBsub]
  exact hdata

end Stellmacher.SectionFour
