module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Symplectic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Ree
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalTrialityExtension

/-!
# Original symplectic and Ree extensions in the Chapter 12 selected pair

The original chosen-module hypotheses supply normalized right Borels and
nonsolvable endpoints for every preparation and perfect selected R. The
symplectic quotient/core calculation and the Ree odd-outer restriction
remove their full original extensions, retaining both inclusion squares.
These comparisons feed the literal residual-preparation theorem together
with the previously checked linear, triality and binary-type reductions.

The marked alternatives are explicit earlier-source inputs. Exhaustive DGS
classification, the remaining unitary and G₂ reductions, prepared recognition,
uniqueness and GlobalExit still require their original assembly. No equation
R = O²(H) or S = T is assumed in constructing these comparisons.

Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6, pp.650--651,
and the literal Chapter 12 setup, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 application of original symplectic-extension collapse. -/
theorem rankOne_global_comparison_of_original_symplectic
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
    (e : Global.OriginalSymplectic.Marking F point L R (Global.sourceS L H)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.concreteComparison_of_original_symplectic
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp F hm hF point e

/-- The literal Chapter 12 application retains every Ree parameter and orientation. -/
theorem rankOne_global_comparison_of_original_ree
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R)
    (m : ℕ) (a : ReeF4.LargeLocalSeeds.Side)
    (e : Global.OriginalRee.Marking m a L R (Global.sourceS L H)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.concreteComparison_of_original_ree
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m a e

/-- The new original rows feed the SAME selected-factor residual preparation.
The premise is broad marked extension data, with no assumed pure comparison. -/
theorem rankOne_global_residual_preparation_of_original_linear_triality_symplectic_ree_and_binary_types
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
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (m : ℕ) (_ : 0 < m) (_ : Nat.card F = 2^m) (point : Bool),
        Nonempty (Global.OriginalSymplectic.Marking F point L R (Global.sourceS L H))) ∨
      (∃ (m : ℕ) (a : ReeF4.LargeLocalSeeds.Side),
        Nonempty (Global.OriginalRee.Marking m a L R (Global.sourceS L H))) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL (![L,R] i ⧸ pCore 2 (![L,R] i)) 2 2) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i ⧸
          pCore 2 (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)) 2 2)) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Group.IsPerfect (residual H) := by
  apply D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique
  intro A B R d hp
  rcases hmark A B R d hp with hlin | htri | hsymp | hree | hlocal | hfull
  · obtain ⟨F,hfield,hfin,hchar,m,hm,hF,point,⟨e⟩⟩ := hlin
    exact D.rankOne_global_comparison_of_original_linear h hmany hn hpsl hH
      d hp F hm hF point e
  · obtain ⟨m,hm,a,⟨e⟩⟩ := htri
    exact D.rankOne_global_comparison_of_original_triality h hmany hn hpsl hH
      d hp m hm a e
  · obtain ⟨F,hfield,hfin,hchar,m,hm,hF,point,⟨e⟩⟩ := hsymp
    exact D.rankOne_global_comparison_of_original_symplectic h hmany hn hpsl hH
      d hp F hm hF point e
  · obtain ⟨m,a,⟨e⟩⟩ := hree
    exact D.rankOne_global_comparison_of_original_ree h hmany hn hpsl hH
      d hp m a e
  · obtain ⟨i,hi⟩ := hlocal
    exact False.elim (d.not_binary_factor_quotient
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp i hi)
  · obtain ⟨i,hi⟩ := hfull
    exact False.elim (d.not_binary_parabolic_quotient
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hp i hi)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
