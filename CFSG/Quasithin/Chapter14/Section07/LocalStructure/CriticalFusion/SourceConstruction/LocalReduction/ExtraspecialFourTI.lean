module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourCentralizers

/-!
# The original TI subgroup in the extraspecial branch

The cyclic and Sylow-central cases were settled when selecting the central
subgroup of order four. In the remaining elementary case, the original fusion
criterion and the now proved outside-centralizer containment establish TI.
This is 14.7.26, with D containing the marked V₁, lying in Z(K) and T, and
having precisely H as its normalizer. The subsequent weak-closure contradiction
on printed p.1054 is not assumed or asserted here.

Source: Aschbacher–Smith 14.7.25–26, printed pp.1052–1053, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual central order-four subgroup is TI, including the noncentral
 elementary case and retaining its original point and normalizer. -/
theorem extraspecial_center_four_ti
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H ∧
      IsTISubgroup D := by
  obtain ⟨D,hZD,hDK,hcard,hDT,hND,hcases⟩ := extraspecial_center_four_ti_reduction
    d h hab structural previous faithful earlier he
  refine ⟨D,hZD,hDK,hcard,hDT,hND,?_⟩
  rcases hcases with ht | ⟨hele,_,hnc⟩
  · exact ht
  let := hele
  apply (extraspecial_four_ti_iff_centralizer_containment
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc).mpr
  intro x hx hxZ
  exact extraspecial_four_outside_centralizer_le
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
