module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.SpecificGroups.PSL2.EightCentralCovers
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import Theory.GroupTheory.GeneralizedFitting.CoprimeOuterSupplement
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Theory.GroupTheory.ExponentFourSylowSections
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Excluding PSL₂(8) in the split Sylow sixteen component branch

Transport the supplied coefficient field of order eight to GF(2³), retaining
the marked central projection. The genuine universal-cover calculation makes
that projection an isomorphism. The full outer automorphism group has order
three by semilinear coverage. Since the ambient quotient by the generalized
Fitting component is a two-group, the component and the supplied Sylow
generate the ambient group; its coprime outer action forces equality.
The resulting order 504 cannot contain the original Sylow of order sixteen.

Source: Aschbacher--Smith F.6.18, printed p.310; GLS III §6.1 for the cover,
and GLS3 Theorem 2.5.12 for the actual outer group. No field carrier,
center-kernel, or outer-order assumption is added to the source model.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.SplitSixteen

/-- A component with central quotient PSL₂(8) cannot have a two-group
ambient extension with a Sylow subgroup of order sixteen. -/
theorem not_psl_two_eight_component_of_sylow_card
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (hT : Nat.card T = 16)
    (K : Subgroup G) [K.Normal] (hFstar : generalizedFitting G = K)
    (hK : IsComponent G K) (hquot : IsPGroup 2 (G ⧸ K))
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 2 8) : False := by
  classical
  subst K
  let _ : IsQuasisimple (generalizedFitting G) := hK.2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  let eF : F ≃+* GaloisField 2 3 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card 2 3 (by decide)]
    rfl)
  let e8 : (generalizedFitting G ⧸ center (generalizedFitting G)) ≃*
      PSL(2, GaloisField 2 3) := e.trans (Theory.PSL2.OuterSolvable.projectiveRingEquiv eF)
  let f := centralQuotientCover e8
  let eK : generalizedFitting G ≃* PSL(2, GaloisField 2 3) :=
    Theory.SpecificGroups.PSL2Eight.coverEquiv f
  have hZ : center (generalizedFitting G) = ⊥ :=
    center_eq_bot_of_centralQuotientEquiv
      Theory.SpecificGroups.PSL2Eight.universalProjection_ker_eq_bot e8
  have houter : Nat.card (MulAut.Outer (generalizedFitting G)) = 3 :=
    (Nat.card_congr (MulAut.outerCongr eK).toEquiv).trans Theory.PSL2.psl_eight_outer_card
  have hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤ := by
    simpa only [sup_comm] using T.sup_eq_top_of_quotient_isPGroup (generalizedFitting G) hquot
  have htop : generalizedFitting G = ⊤ :=
    generalizedFitting_eq_top_of_coprime_outer_supplement T hgen hZ (by
      rw [houter]
      decide)
  have hcard : Nat.card (generalizedFitting G) = 504 := by
    rw [Nat.card_congr eK.toEquiv]
    rw [← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,
      GaloisField.card 2 3 (by decide)]
    norm_num
  rw [htop, card_top] at hcard
  have hdiv := (T : Subgroup G).card_subgroup_dvd_card
  rw [hT, hcard] at hdiv
  norm_num at hdiv

/-- The original split C₂ × D₈ Sylow discharges the order-sixteen premise. -/
theorem not_psl_two_eight_component
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) [K.Normal] (hFstar : generalizedFitting G = K)
    (hK : IsComponent G K) (hquot : IsPGroup 2 (G ⧸ K))
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 2 8) : False :=
  not_psl_two_eight_component_of_sylow_card T
    ((Nat.card_congr eT.toEquiv).trans split_sixteen_card) K hFstar hK hquot hmodel

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.SplitSixteen
