module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Triality
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFiveField
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.BinaryTypes
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalLinearExtension

/-!
# Original extension reductions for the Chapter 12 selected pair

The literal chosen-module input supplies the original normalized-Borel
hypotheses to the triality extension collapse. The resulting compatible
comparison is valid for every preparation and perfect selected R, before
identifying R with O²(H). Together with the earlier linear collapse and the
binary quotient exclusions, it feeds the existing residual-preparation
consumer and retains its independent uniqueness premise.

The unitary-five application separately forces q = 4 from an original
extension endpoint, with no prior extension collapse. The source assembly
must still construct exhaustive marked alternatives; symplectic, G₂, Ree,
unitary and degree-two unitary extension reductions, prepared recognition,
uniqueness and final GlobalExit retain their original owners and obligations.
These are conditional source reductions, not unconditional classification.

Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6, pp.650--651,
and the literal Chapter 12 application, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Apply original triality-extension collapse to any selected perfect right
factor in the literal Chapter 12 setup. -/
theorem rankOne_global_comparison_of_original_triality
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R)
    (m : ℕ) (hm : 0 < m) (a : _root_.Triality.Standard.Parabolics.Node)
    (e : Global.OriginalTriality.Marking m hm a L R (Global.sourceS L H)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.concreteComparison_of_original_triality
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm a e

/-- The selected-factor consumer for the proved original extension rows and
binary quotient type clauses. Genuine DGS exhaustiveness and the other rows
remain upstream. No binary type-to-model implication is used. -/
theorem rankOne_global_residual_preparation_of_original_linear_triality_and_binary_types
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hmark : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R →
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (m : ℕ) (_ : 0 < m) (_ : Nat.card F = 2^m) (point : Bool),
        Nonempty (Global.OriginalLinear.Marking L R (Global.sourceS L H) F point)) ∨
      (∃ (m : ℕ) (hm : 0 < m) (a : _root_.Triality.Standard.Parabolics.Node),
        Nonempty (Global.OriginalTriality.Marking m hm a L R (Global.sourceS L H))) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL (![L,R] i ⧸ pCore 2 (![L,R] i)) 2 2) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i ⧸
          pCore 2 (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)) 2 2)) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Group.IsPerfect (residual H) := by
  apply D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique
  intro A B R d hp
  rcases hmark A B R d hp with hlin | htri | hlocal | hfull
  · obtain ⟨F, hfield, hfin, hchar, m, hm, hF, point, ⟨e⟩⟩ := hlin
    exact D.rankOne_global_comparison_of_original_linear h hmany hn hpsl hH
      d hp F hm hF point e
  · obtain ⟨m,hm,a,⟨e⟩⟩ := htri
    exact D.rankOne_global_comparison_of_original_triality h hmany hn hpsl hH
      d hp m hm a e
  · obtain ⟨i,hi⟩ := hlocal
    exact False.elim (d.not_binary_factor_quotient
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp i hi)
  · obtain ⟨i,hi⟩ := hfull
    exact False.elim (d.not_binary_parabolic_quotient
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hp i hi)

/-- Apply the existing unitary-five rank obstruction to an original extension
endpoint in the literal chosen-module setup, for either orientation. -/
theorem rankOne_global_original_unitaryFive_extension_field
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {R : Subgroup G} {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    (M : ChapterF.GreenBook.UnitaryFive.Model q)
    {E : Type*} [Group E] (i : Fin 2)
    (f : ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i →* E)
    (hf : Function.Injective f)
    (j : M.leftParabolic →* E) (hj : Function.Injective j)
    (hbase : j.range ≤ f.range) : q = 4 :=
  Global.original_unitaryFive_extension_field
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hq heven M i f hf j hj hbase

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
