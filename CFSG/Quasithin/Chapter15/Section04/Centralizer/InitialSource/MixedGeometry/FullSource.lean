module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.FFInputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.Quotient.FullSource

/-!
# The original mixed source branch through complete source recognition

The original member and double residual pair construct their component inputs,
kill the non-two-core branch, and produce the elementary conjugate span and
actual FF action. Complete corrected F-source and adequate B-source comparison
recognizes the actual two-core quotient as S3 by S3. Its normalization conflicts
with the source exchange and the distinct unique maximal overgroups.

No fitting, module, FF, quotient, local-action or normalization conclusion is
assumed. The only independent classification parameters are the full earlier
ABC, corrected F.6.18 and adequate complete B.5 statements.
Source: Aschbacher--Smith,15.4.18, pp.1162--1163.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure LocalSetup LocalSetup.SourceWitnesses
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal LocalSetup.TwoFactors.FFBranch
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Complete source recognition contradicts the same actual mixed setup. -/
theorem source_mixed_contradiction {κ : GroupClass.{u}}
    (hABC : ∀ (A : Type u) [Group A] [Finite A], ChapterA.Section02.TheoremsABC κ A)
    (sourceF : FSource.SourceClassificationInput κ)
    (sourceB : ClassificationComparison.FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u} κ)
    {T : Sylow 2 G} {M₁ M₂ Y X : Subgroup G}
    (hY : Input κ T M₁ Y 1) (hX : Input κ T M₂ X 2) (p : Pair T M₂ X)
    (d : RealizedFactors T Y X M₁ M₂ p.quotient.factor)
    (c : Configuration κ T Y X M₂ p.quotient.factor)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) : False := by
  let F := p.quotient.factor
  let I := generated T Y F
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let A := (firstGroup T Y F).subgroupOf I
  let B := (secondGroup T F).subgroupOf I
  have hF := source_mixed_generalizedFitting hABC sourceF hY hX p d c hZ
  obtain ⟨P,hP,hC,hm,hJ,_⟩ := source_mixed_FF_inputs hY d c hF
  let := hm
  have hB : ChapterB.baumann (T : Subgroup G) ≤ (P : Subgroup I).map I.subtype := by
    rw [hP]
    exact le_inf inf_le_left d.baumann_invariant
  have hZI : Z ≤ I := by
    apply le_trans ((centralOmega_le_thompsonAlpha _).trans (alpha_le_baumann _))
    exact (le_inf inf_le_left d.baumann_invariant).trans (le_sup_right.trans le_sup_left)
  have hne : (pCore 2 A).map A.subtype ≠ (pCore 2 B).map B.subtype := by
    have hk : IsPGroup 2 I.subtype.ker := by
      rw [ker_subtype]
      exact IsPGroup.of_bot
    intro he
    apply c.different_cores
    have hh := congrArg (map I.subtype) he
    change (A.pCoreIn 2).map I.subtype = (B.pCoreIn 2).map I.subtype at hh
    rw [map_pCoreIn_of_ker_isPGroup I.subtype hk,
      map_pCoreIn_of_ker_isPGroup I.subtype hk,
      map_subgroupOf_eq_of_le (show firstGroup T Y F ≤ I from le_sup_left),
      map_subgroupOf_eq_of_le (show secondGroup T F ≤ I from le_sup_right)] at hh
    exact hh
  have hgen : Y ⊔ F false ⊔ (P : Subgroup I).map I.subtype = I := by
    rw [hP]
    change Y ⊔ F false ⊔ stabilizer T F =
      (Y ⊔ stabilizer T F) ⊔ (F false ⊔ stabilizer T F)
    ac_rfl
  have hZY : ⁅Z,Y⁆ ≠ ⊥ := by
    intro he
    exact source_member_central_commutator hY (by rw [he,inf_bot_eq])
  obtain ⟨e⟩ := FFBranch.FullSource.mixed_symmetricThreeProduct_quotient sourceF sourceB T I Y
    (F false) Z P A B c.sqtk c.goldschmidt hne hC hB hZI
    (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right) hF hgen
    (by simpa only [ChapterB.thompsonJ_zero] using d.thompson_commutator₁.symm)
    (by simpa only [ChapterB.thompsonJ_zero] using d.thompson_commutator₂.symm) hZY hJ
  exact source_mixed_quotient_contradiction hY d c e

end CFSG.Quasithin.Chapter15.Section04.InitialSource
