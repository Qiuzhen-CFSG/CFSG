module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Preparation
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Models
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Intersection
public import Theory.GroupTheory.SolvableResidual.CoreOuter

/-!
# The terminal residual and product structure from its precise source inputs

The permitted 14.6.18 input identifies the radical with the two-core by
`Classification.Preparation`. The actual residual quotient models give a
two-group outer action, so the canonical solvable residual is O²(Mc).
The original Sylow T then supplements it, including the literal set product.
Combining this with the seed-quotient centralizer input yields M=LT and
M∩Mc=T on the same original subgroups.

These are conditional deductions of 14.6.23(1--2), not the completed source
theorem: 14.6.20--21 must still construct `ResidualQuotientModels`, and
qt-e-terminal-natural-support-decomposition must construct
`SeedQuotientCentralizerBound`. Final discharge remains with
qt-e-terminal-component-alternatives. Original 14.6.18 remains an allowed
explicit premise owned by qt-e-14625-source.

Source: Aschbacher--Smith, printed pp.1037--1038.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)

include hG hempty hM hunique hmany hcard e hab hsolv

/-- The residual assertion of 14.6.23(1), conditional on the actual residual
quotient model supplied by the component classification. -/
theorem terminal_residual_structure_of_models
    (hm : ResidualQuotientModels (solvableResidual (Mc ⧸ pCore 2 Mc))) :
    solvableResidual Mc = pResidual 2 Mc ∧
      (Mc : Set G) = ((solvableResidual Mc).map Mc.subtype : Set G) *
        ((T : Subgroup G) : Set G) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hTH : (T : Subgroup G) ≤ Mc := hout.1.2
  have hr := source_radical_eq_core hG T hempty hM hunique hmany hcard e hab hsolv Mc hout
  have he := residuals_eq_of_core_outer hr hm.outer_isTwoGroup
  refine ⟨he,?_⟩
  let R := (solvableResidual Mc).map Mc.subtype
  have hj : R ⊔ (T : Subgroup G) = Mc := by
    have hh := congrArg (Subgroup.map Mc.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hTH))
    rw [←he,Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hn : Mc ≤ normalizer (R : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (solvableResidual Mc).le_normalizer_map Mc.subtype
  exact (congrArg (fun X : Subgroup G => (X : Set G)) hj.symm).trans
    (coe_mul_of_right_le_normalizer_left R (T : Subgroup G) (hTH.trans hn))

/-- Both structural clauses, keeping the remaining component-model and
natural-module inputs explicit. The final source assembly must discharge them. -/
theorem terminal_structure_of_models_and_seed_centralizer
    (hm : ResidualQuotientModels (solvableResidual (Mc ⧸ pCore 2 Mc)))
    (hc : SeedQuotientCentralizerBound T M Mc) :
    solvableResidual Mc = pResidual 2 Mc ∧
      (Mc : Set G) = ((solvableResidual Mc).map Mc.subtype : Set G) *
        ((T : Subgroup G) : Set G) ∧
      (M : Set G) = (sourceResidual M Mc : Set G) * ((T : Subgroup G) : Set G) ∧
      M ⊓ Mc = (T : Subgroup G) := by
  obtain ⟨hr,hH⟩ := terminal_residual_structure_of_models
    hG T hempty hM hunique hmany hcard e hab hsolv hm
  obtain ⟨hM,hI⟩ := terminal_product_of_seed_quotient_centralizer
    hG T hempty hM hunique hmany hcard e hc
  exact ⟨hr,hH,hM,hI⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification
