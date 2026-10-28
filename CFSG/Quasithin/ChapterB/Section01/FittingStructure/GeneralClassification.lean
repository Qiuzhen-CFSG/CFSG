module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.FactorSelection

/-!
# Applying B.1.9 to the B.5 Fitting reduction

The completed B.1.9 construction supplies the existing universal `EarlierB19`
interface without changing its groups, relative odd cores, product maps or
support inclusions. Its noncentrality convention is equivalent to the literal
nonzero Fitting commutator. The actual B.5 consumer below now selects the
original S₃ factor and its complementary action without an earlier-B.1.9
premise. The remaining B.5 induction and classification inputs stay with that
source theorem's owner.

Source: Aschbacher–Smith, B.1.9, printed pp.71–72, and B.5.8, printed p.106.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- Preserve every original inclusion when adapting to the B.5 source contract. -/
def Conclusion.toB19Conclusion (d : Conclusion ρ) :
    SourceInduction.FittingReduction.B19Conclusion ρ where
  count := d.count
  factor := d.factor
  factorModel := d.factorModel
  groupProduct := d.groupProduct
  groupProduct_single := d.groupProduct_single
  groupProduct_residual := d.groupProduct_residual
  oddFactor := d.oddFactor
  oddFactor_eq := d.oddFactor_eq
  oddFactorModel := d.oddFactorModel
  oddProduct := d.oddProduct
  oddProduct_single := d.oddProduct_single
  fittingProduct := d.fittingProduct
  fittingProduct_apply := d.fittingProduct_apply
  moved_eq := d.moved_eq
  dimension := d.dimension
  moduleSum := d.moduleSum
  moduleSum_single := d.moduleSum_single
  noncentral_offenders := by
    intro A
    rw [← d.noncentral_offenders A]
    apply and_congr_right
    intro _
    exact not_congr (commutator_eq_bot_iff_le_centralizer.trans le_centralizer_iff).symm
  moved_subgroup_centralizes := d.moved_subgroup_centralizes

/-- The full earlier B.1.9 input required by B.5, with no additional premises. -/
theorem earlierB19 : SourceInduction.FittingReduction.EarlierB19.{u,v} := by
  intro G _ _ V _ _ _ ρ hρ hcore hF
  obtain ⟨d⟩ := source_lemma_B_1_9 ρ hρ hcore hF
  exact ⟨d.toB19Conclusion⟩

end CFSG.Quasithin.ChapterB.FittingStructure

namespace CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
universe u v
variable {G : Type u} [Group G] [Finite G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}

/-- B.1.9 constructs the factor configuration used by B.5.8 on its actual
faithful FF action. The universal B.1.9 input is fully discharged. -/
theorem FFHypothesis.fitting_configuration_of_source (hyp : FFHypothesis K ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hn : ¬ A ≤ centralizer (fittingSubgroup G : Set G)) :
    Nonempty (Configuration ρ A) :=
  FFHypothesis.fitting_configuration hyp FittingStructure.earlierB19 hA hn

end CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
