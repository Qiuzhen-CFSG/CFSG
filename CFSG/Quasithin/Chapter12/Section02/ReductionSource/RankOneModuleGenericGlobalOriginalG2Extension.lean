module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.G2
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalSymplecticReeExtension

/-!
# Original G₂ extensions in the literal Chapter 12 selected pair

For every preparation and perfect selected R, the native short-local quotient
calculation removes a marked original G₂ extension. The same comparison maps
retain both squares on the entire Borel. Together with the previously proved
linear, symplectic, triality, Ree and binary-type restrictions, this feeds the
literal residual-preparation theorem.

The displayed marked alternatives are earlier-source inputs, whose construction
and exhaustiveness remain with the DGS source assembly. The unitary original
extensions, prepared-U₅ recognition, uniqueness and GlobalExit retain their
existing obligations. This conditional application does not assert exhaustive
source classification or identify an arbitrary selected R with the residual.

Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6, pp.650--651,
and the Chapter 12 chosen-module setup, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Apply original G₂ extension collapse before identifying the selected factor. -/
theorem rankOne_global_comparison_of_original_g2
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2] (short : Bool)
    (e : Global.OriginalG2.Marking F short L R (Global.sourceS L H)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.concreteComparison_of_original_g2
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp F short e

/-- The new original rows feed the SAME selected-factor residual preparation.
The premise is broad marked extension data, with no assumed pure comparison. -/
theorem rankOne_global_residual_preparation_of_original_linear_triality_symplectic_ree_g2_and_binary_types
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
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (short : Bool),
        Nonempty (Global.OriginalG2.Marking F short L R (Global.sourceS L H))) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL (![L,R] i ⧸ pCore 2 (![L,R] i)) 2 2) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i ⧸
          pCore 2 (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)) 2 2)) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Group.IsPerfect (residual H) := by
  apply D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique
  intro A B R d hp
  rcases hmark A B R d hp with hlin | htri | hsymp | hree | hg2 | hlocal | hfull
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
  · obtain ⟨F,hfield,hfin,hchar,short,⟨e⟩⟩ := hg2
    exact D.rankOne_global_comparison_of_original_g2 h hmany hn hpsl hH
      d hp F short e
  · obtain ⟨i,hi⟩ := hlocal
    exact False.elim (d.not_binary_factor_quotient
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp i hi)
  · obtain ⟨i,hi⟩ := hfull
    exact False.elim (d.not_binary_parabolic_quotient
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hp i hi)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
