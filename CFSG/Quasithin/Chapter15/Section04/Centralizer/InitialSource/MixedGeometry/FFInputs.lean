module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.ComponentSource
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ActionGroup
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.OffenderTransfer

/-!
# Literal FF inputs and the terminal mixed normalization contradiction

On the same mixed group and its original central-omega seed, the specified
Sylow is exactly the seed centralizer. The proved fitting conclusion makes
the seed's normal closure elementary. The actual Thompson image belongs to
the best-offender subgroup, and the moving first factor supplies an FF witness.
Full earlier ABC and corrected F-source classification construct this entire
input on the actual maps.

Separately, an S3-by-S3 quotient normalizes the original first factor. The
source exchange and unique maximal overgroups show the second factor cannot
do so, giving the final contradiction. Quotient recognition itself remains
with the full-source FF comparison.

Source: Aschbacher--Smith, final paragraph of15.4.18, p.1163.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure LocalSetup LocalSetup.SourceWitnesses
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal LocalSetup.TwoFactors.FFBranch
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem source_factor_outside {T : Sylow 2 G} {Y X M₁ M₂ : Subgroup G}
    {F : Bool → Subgroup G} (d : RealizedFactors T Y X M₁ M₂ F) :
    ¬ F false ≤ normalizer (Y : Set G) := by
  have hswap : (F false).map (MulAut.conj d.swapper).toMonoidHom = F true := by
    have he := d.pairAction.conjugation ⟨d.swapper,d.sylow_le₂ d.swapper_mem⟩ false
    cases hp : d.pairAction.permutation ⟨d.swapper,d.sylow_le₂ d.swapper_mem⟩ false with
    | false => exact (d.swapper_moves (mem_normalizer_iff_map_conj_eq.mpr
        (he.trans (congrArg F hp)))).elim
    | true => exact he.trans (congrArg F hp)
  have hjoin := pair_join_eq_of_swap d.product d.swapper_mem hswap
  intro hn
  have hXT : X ⊔ (T : Subgroup G) ≤ M₁ := by
    rw [← hjoin]
    exact sup_le (hn.trans_eq d.normalizer₁.symm) d.sylow_le₁
  exact d.different (d.unique₂ M₁ d.maximal₁ hXT)

/-- Recognition of the actual quotient closes the raw source branch. -/
theorem source_mixed_quotient_contradiction {κ : GroupClass.{u}}
    {T : Sylow 2 G} {Y X M₁ M₂ : Subgroup G} {F : Bool → Subgroup G}
    (hY : Input κ T M₁ Y 1) (d : RealizedFactors T Y X M₁ M₂ F)
    (c : Configuration κ T Y X M₂ F)
    (e : (generated T Y F ⧸ pCore 2 (generated T Y F)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : False := by
  obtain ⟨P,hP⟩ := c.generated_sylow
  have hPT : (P : Subgroup (generated T Y F)).map (generated T Y F).subtype ≤ T := by
    rw [hP]
    exact inf_le_left
  have hB : ChapterB.baumann (T : Subgroup G) ≤
      (P : Subgroup (generated T Y F)).map (generated T Y F).subtype := by
    rw [hP]
    exact le_inf inf_le_left d.baumann_invariant
  exact contradiction_of_symmetricThreeProduct_quotient T (generated T Y F) Y (F false) P
    hPT hB (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right)
    (YFamily.perfect hY.member) (d.sylow_le₁.trans d.normalizer₁.le)
    (by simpa only [ChapterB.thompsonJ_zero] using d.thompson_commutator₁.symm)
    (by simpa only [ChapterB.thompsonJ_zero] using d.thompson_commutator₂.symm)
    (source_factor_outside d) e

/-- The actual conjugate span supplies the full FF witness and Thompson containment. -/
theorem source_mixed_FF_inputs {κ : GroupClass.{u}}
    {T : Sylow 2 G} {Y X M₁ M₂ : Subgroup G} {F : Bool → Subgroup G}
    (hY : Input κ T M₁ Y 1) (d : RealizedFactors T Y X M₁ M₂ F)
    (c : Configuration κ T Y X M₂ F)
    (hF : generalizedFitting (generated T Y F) = pCore 2 (generated T Y F)) :
    let I := generated T Y F
    let Z := (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf I
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = stabilizer T F ∧
      ∃ hC : centralizer (Z : Set I) = (P : Subgroup I),
      ∃ hm : IsElementaryAbelian 2 (moduleClosure Z),
      let := hm
      (elementaryAbelianMaxJ (P : Subgroup I)).map coreProjection ≤ offenderGroup P Z hC ∧
        Representation.BinaryOffender.IsFFModule (quotientAction P Z hC) := by
  let I := generated T Y F
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  obtain ⟨P,hP⟩ := c.generated_sylow
  have hPT : (P : Subgroup I).map I.subtype ≤ T := by rw [hP]; exact inf_le_left
  have hB : ChapterB.baumann (T : Subgroup G) ≤ (P : Subgroup I).map I.subtype := by
    rw [hP]
    exact le_inf inf_le_left d.baumann_invariant
  have hZI : Z ≤ I := by
    apply le_trans ((centralOmega_le_thompsonAlpha _).trans (alpha_le_baumann _))
    exact (le_inf inf_le_left d.baumann_invariant).trans (le_sup_right.trans le_sup_left)
  have hYI : Y ≤ I := le_sup_left.trans le_sup_left
  have hC := centralizer_seed_subgroupOf I (T : Subgroup G) Z P T.isPGroup' hPT hZI hY.center_centralizer
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (Z.subgroupOf I) := IsElementaryAbelian.subgroupOf hZI
  let hm := moduleClosure_elementary P (Z.subgroupOf I) hC hF
  let := hm
  refine ⟨P,hP,hC,hm,?_,?_⟩
  · apply Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.thompson_image_le_offender
      (P : Subgroup I) (moduleClosure (Z.subgroupOf I))
      ((moduleClosure_le_twoCore P (Z.subgroupOf I) hC hF).trans (pCore_isPGroup.le_sylow_of_normal P))
      coreProjection ((QuotientGroup.ker_mk' _).trans (moduleClosure_centralizer P (Z.subgroupOf I) hC).symm)
      (quotientAction P (Z.subgroupOf I) hC)
    exact quotientAction_apply P (Z.subgroupOf I) hC
  · have hJ := thompson_sylow_image_of_baumann I T P hB
    have hYJ := factor_commutator_subgroupOf I Y _ _ hYI hJ
      (show Y = ⁅Y,elementaryAbelianMaxJ (T : Subgroup G)⁆ from by
        simpa only [ChapterB.thompsonJ_zero] using d.thompson_commutator₁.symm)
    apply quotientAction_isFFModule P (Z.subgroupOf I) hC (Y.subgroupOf I) hF hYJ
    apply seed_factor_commutator_ne_bot_subgroupOf I Z Y hZI hYI
    intro he
    have hn := source_member_central_commutator hY
    exact hn (by rw [he,inf_bot_eq])

open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

/-- Original source inputs construct the FF data, including the fitting step. -/
theorem source_mixed_FF_inputs_of_classifications {κ : GroupClass.{u}}
    (hABC : ∀ (A : Type u) [Group A] [Finite A], ChapterA.Section02.TheoremsABC κ A)
    (sourceF : FSource.SourceClassificationInput κ)
    {T : Sylow 2 G} {M₁ M₂ Y X : Subgroup G}
    (hY : Input κ T M₁ Y 1) (hX : Input κ T M₂ X 2) (p : Pair T M₂ X)
    (d : RealizedFactors T Y X M₁ M₂ p.quotient.factor)
    (c : Configuration κ T Y X M₂ p.quotient.factor)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) :
    let I := generated T Y p.quotient.factor
    let Z := (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf I
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = stabilizer T p.quotient.factor ∧
      ∃ hC : centralizer (Z : Set I) = (P : Subgroup I),
      ∃ hm : IsElementaryAbelian 2 (moduleClosure Z),
      letI := hm
      (elementaryAbelianMaxJ (P : Subgroup I)).map coreProjection ≤ offenderGroup P Z hC ∧
        Representation.BinaryOffender.IsFFModule (quotientAction P Z hC) :=
  source_mixed_FF_inputs hY d c (source_mixed_generalizedFitting hABC sourceF hY hX p d c hZ)

end CFSG.Quasithin.Chapter15.Section04.InitialSource
