module
public import Stellmacher.SectionFiveToSeven.Result6_1
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSymmetry
public import Stellmacher.SectionFiveToSeven.SixTwoLocalCentralization
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSectionThree
public import Stellmacher.SectionFiveToSeven.PFamilyBridge
public import Stellmacher.SectionFiveToSeven.Result5_3
public import Stellmacher.SectionThree.LemmaThreeFour
public import Stellmacher.BaumannNormalizer

/-!
# Stellmacher (6.2): Thompson noncontainment in both local cores

Under Hypothesis Two, if P₂ acts nontrivially on the central involutions
of the common Sylow subgroup S, then J(S) is contained in neither local
two-core. The noncentral assumption makes the hypotheses symmetric and
also gives nontrivial action by P₁. Applying the proved (6.1) in both
orders shows that the Baumann subgroup lies in neither core.

The Baumann subgroup is normal in S, so (3.4) makes its commutator with
each local residual equal that residual. If J(S) lay in a local core,
the local centralization lemma, using characteristic two from (5.3),
would force the corresponding member to centralize the central involutions
of S, contradicting its nontrivial action.

Source: Stellmacher (6.2), Journal of Algebra 190 (1997), p.30,
`refs/latex/stellmacher-n-group.tex`. The public noncontainment statement
matches the journal scan; all local subgroups and shared Sylow data are
retained exactly.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

/-- **Stellmacher (6.2).** Nontrivial action by the second member forces
Thompson noncontainment in both local two-cores. -/
public theorem lemma_six_two
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ ≠ ⊥) :
    ¬ elementaryAbelianMaxJ (G := H) S ≤ twoCoreIn P1 ∧
      ¬ elementaryAbelianMaxJ (G := H) S ≤ twoCoreIn P2 := by
  have hswap := h.swap_of_commutator_ne_bot S0 S P1 P2 hcomm
  have hleft := h.left_commutator_ne_bot S0 S P1 P2 hcomm
  have hB1 := lemma_six_one S0 S P2 P1 hswap
  have hB2 := lemma_six_one S0 S P1 P2 h
  obtain ⟨hsol1,hchar1,hsol2,hchar2⟩ := lemma_five_three S0 S P1 P2 h
  have hBnorm : ((baumannIn S).subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (show baumannIn S ≤ S from inf_le_left)).mpr
      (S.le_normalizer.trans (normalizer_le_normalizer_baumann S))
  have hres (P : Subgroup H) (hP : P ∈ PFamily ⊤ S)
      (hsol : Group.IsSolvable P) (hB : ¬ baumannIn S ≤ twoCoreIn P) :
      ⁅twoResidualIn P, baumannIn S⁆ = twoResidualIn P := by
    rcases SectionThree.lemma_three_four S h.sectionThreeHypotheses P
        ((pFamily_iff_pSet ⊤ S P).mp hP) (baumannIn S) ⟨inf_le_left,hBnorm⟩ hsol with
      hc | hr
    · exact (hB hc).elim
    · exact hr
  constructor
  · intro hJ
    exact hleft (sixTwo_local_centralization S P1 h.fiveOne.P1_mem.1.2.1 hchar1 hJ
      (hres P1 h.fiveOne.P1_mem hsol1 hB1))
  · intro hJ
    exact hcomm (sixTwo_local_centralization S P2 h.fiveOne.P2_mem.1.2.1 hchar2 hJ
      (hres P2 h.fiveOne.P2_mem hsol2 hB2))

end Stellmacher.SectionsFiveToSeven
