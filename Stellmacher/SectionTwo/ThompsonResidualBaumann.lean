module
public import Stellmacher.SectionTwo.ThompsonThreeCoreBaumann
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# Baumann containment forced by a smaller Thompson residual commutator

For a solvable local P-set group, let T lie inside its supplied Sylow
subgroup, containing the Section Two module and quotient kernel. Suppose
J(T) is normal in the Sylow subgroup, lies outside the two-core, and the
full residual image in the faithful module quotient has odd order.
Then the literal Baumann subgroup lies in T.

Lemma (3.4) says that J(T) generates the full residual by commutators.
The odd residual image lies in the quotient's odd core, so its commutator
equality places it in the selected product for J(T). The three-core lies
in the two-residual because its image in a two-group is trivial. Thus
the selected product contains the three-core, and the previously proved
Thompson-action comparison lifts the desired Baumann containment.

This is the source (3.4) step in the final action comparison of Stellmacher
(8.3), journal p38, retaining the original Section Two action and module.
Source: refs/latex/stellmacher-n-group.tex.
-/

open BenderSuzuki.External
namespace Stellmacher.SectionTwo
universe u

public theorem baumann_le_of_thompson_residual
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (h3 : SectionThree.Hypotheses G (S : Subgroup G))
    (hP : (⊤ : Subgroup G) ∈ SectionThree.PSet ⊤ (S : Subgroup G))
    {X : Type u} [Group X] [Finite X]
    (q : G →* X) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (B T : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (hTS : T ≤ (S : Subgroup G)) (hVT : vSubgroup S ≤ T) (hCT : q.ker ≤ T)
    (hJn : ((elementaryAbelianMaxJ T).subgroupOf (S : Subgroup G)).Normal)
    (hnot : ¬ elementaryAbelianMaxJ T ≤ twoCoreAmbient (⊤ : Subgroup G))
    (hodd : Odd (Nat.card ((twoResidualAmbient (⊤ : Subgroup G)).map q))) :
    letI : IsElementaryAbelian 2 (vSubgroup S) :=
      (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
    letI := quotientConjugationAction S q hq hker
    SectionOne.Hypotheses X (vSubgroup S) → B ≤ T := by
  let _ : IsElementaryAbelian 2 (vSubgroup S) :=
    (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let _ := quotientConjugationAction S q hq hker
  intro hOne
  let _ : Group.IsSolvable G := h.solvable
  have hcomm := (SectionThree.lemma_three_four (S : Subgroup G) h3 ⊤ hP
    (elementaryAbelianMaxJ T) ⟨(sSup_le fun _ ha => ha.1).trans hTS, hJn⟩
    (inferInstance : Group.IsSolvable (⊤ : Subgroup G))).resolve_left hnot
  let R := hktPResidual 2 X
  let _ : R.Normal := hktPResidual_normal
  have hRmap : (twoResidualAmbient (⊤ : Subgroup G)).map q = R := by
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual,
      hktPResidual_map_of_surjective' q hq]
  have hRodd : Odd (Nat.card R) := hRmap ▸ hodd
  have hRcore : R ≤ pPrimeCore 2 X := le_sSup ⟨inferInstance, hRodd.coprime_two_left⟩
  have hthreeR : pCore 3 X ≤ R := by
    let r := QuotientGroup.mk' R
    have h3map := (pCore_isPGroup (p := 3) (G := X)).map r
    have h2map := (hktPResidual_quotient_isPGroup (q := 2) (Q := X)).to_subgroup
      ((pCore 3 X).map r)
    have hb : (pCore 3 X).map r = ⊥ := disjoint_self.mp
      (IsPGroup.disjoint_of_ne 3 2 (by decide) _ _ h3map h2map)
    simpa only [r, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hb
  have hRcomm : ⁅R, (elementaryAbelianMaxJ T).map q⁆ = R := by
    have hm := congrArg (Subgroup.map q) hcomm
    rwa [Subgroup.map_commutator, hRmap] at hm
  have hthree : pCore 3 X ≤ ⁅pPrimeCore 2 X, (elementaryAbelianMaxJ T).map q⁆ ⊔
      (elementaryAbelianMaxJ T).map q := by
    apply hthreeR.trans
    rw [← hRcomm]
    exact (Subgroup.commutator_mono hRcore le_rfl).trans le_sup_left
  exact baumann_le_of_thompson_image_threeCore h S q hq hker B T hB hTS hVT hCT hthree hOne

end Stellmacher.SectionTwo

