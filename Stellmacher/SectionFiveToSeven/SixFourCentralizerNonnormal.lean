module
public import Stellmacher.SectionFiveToSeven.Result6_1
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSectionThree
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannTwoOvergroupNormalizer
public import Stellmacher.SectionThree.LemmaThreeSeven

/-!
# Nonnormality of the centralizer residual join in (6.4)

Under Hypothesis Two with S the global Sylow subgroup, let B(S) ≤ T ≤ S
and T ≤ C, where C together with S generates P₂. Then O²(C) joined with T
does not normalize T. In the application C=C_{P₂}(w) and T=C_S(w).
No Sylow hypothesis for T inside C is needed for this assertion.

If the residual join normalized T, Baumann heredity would make O²(C)
normalize B(S). Choose any Sylow subgroup of C containing B(S); the global
Baumann two-overgroup theorem makes this Sylow normalize B(S) as well.
The residual-Sylow generation identity then makes C, and hence P₂, normalize
B(S). That puts B(S) in O₂(P₂), contradicting (6.1).

This proves the nonnormality sentence in Stellmacher (6.4), Journal of
Algebra 190 (1997), p.32, without assuming the subsequent factor extraction.
Source: `refs/latex/stellmacher-n-group.tex` and the fuller journal proof in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixFour_centralizer_residual_join_not_normalize
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2) (hS : S = (S0 : Subgroup H))
    (C T : Subgroup H) (hBT : baumannIn S ≤ T) (hTS : T ≤ S)
    (hTC : T ≤ C) (hgen : C ⊔ S = P2) :
    ¬ twoResidualAmbient C ⊔ T ≤ Subgroup.normalizer (T : Set H) := by
  intro hnormal
  have hBTeq : baumannIn T = baumannIn S := baumann_eq_of_intermediate S T hBT hTS
  have hRnorm : twoResidualAmbient C ≤ Subgroup.normalizer (baumannIn S : Set H) := by
    rw [← hBTeq]
    exact (le_sup_left.trans hnormal).trans (normalizer_le_normalizer_baumann T)
  have hBC : baumannIn S ≤ C := hBT.trans hTC
  have hBp : IsPGroup 2 (baumannIn S) :=
    h.sectionThreeHypotheses.nontrivial_two_subgroup.2.to_le inf_le_left
  have hBCp : IsPGroup 2 ((baumannIn S).subgroupOf C) :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBC).symm
  obtain ⟨R, hBR⟩ := hBCp.exists_le_sylow
  let Ra : Subgroup H := (R : Subgroup C).map C.subtype
  have hBRa : baumannIn S ≤ Ra := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hBC]
    exact Subgroup.map_mono hBR
  have hRanorm : Ra ≤ Subgroup.normalizer (baumannIn S : Set H) := by
    have hBRa0 : baumannIn (S0 : Subgroup H) ≤ Ra := hS ▸ hBRa
    have hh := Stellmacher.twoSubgroup_le_normalizer_baumann S0 Ra
      (R.isPGroup'.map C.subtype) (by
        simpa [baumannIn, omegaOneCenter, omegaOneCenterAmbient] using hBRa0)
    rw [hS]
    simpa only [baumannIn, omegaOneCenter, omegaOneCenterAmbient] using hh
  have hCnorm : C ≤ Subgroup.normalizer (baumannIn S : Set H) := by
    rw [← SectionThree.twoResidual_sup_sylowImage (show IsSylowSubgroupIn Ra C from ⟨R, rfl⟩)]
    exact sup_le hRnorm hRanorm
  have hSnorm : S ≤ Subgroup.normalizer (baumannIn S : Set H) :=
    S.le_normalizer.trans (normalizer_le_normalizer_baumann S)
  have hPnorm : P2 ≤ Subgroup.normalizer (baumannIn S : Set H) := by
    rw [← hgen]
    exact sup_le hCnorm hSnorm
  have hBP : baumannIn S ≤ P2 :=
    (inf_le_left : baumannIn S ≤ S).trans h.fiveOne.P2_mem.1.2.1.1
  let _ : ((baumannIn S).subgroupOf P2).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mpr hPnorm
  have hBPp : IsPGroup 2 ((baumannIn S).subgroupOf P2) :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBP).symm
  have hcore : (baumannIn S).subgroupOf P2 ≤ pCore 2 P2 :=
    le_sSup ⟨inferInstance, hBPp⟩
  apply lemma_six_one S0 S P1 P2 h
  rw [← Subgroup.map_subgroupOf_eq_of_le hBP]
  exact Subgroup.map_mono hcore

end Stellmacher.SectionsFiveToSeven
