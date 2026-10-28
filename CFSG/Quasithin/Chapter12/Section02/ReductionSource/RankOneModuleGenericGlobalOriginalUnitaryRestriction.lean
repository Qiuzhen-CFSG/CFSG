module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourRestriction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFiveRestriction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalG2Extension

/-!
# Broad original extension markings exclude the Chapter 12 diagram branch

Apply the actual diagram selector to obtain the same perfect R, its binary
PSL₂ quotient and its two noncentral core layers. The published linear,
symplectic, G₂, triality and Ree extension restrictions give the comparisons
needed by their existing exclusions. The new unitary-four native-base
restriction and unitary-five residual quotient argument exclude their broad
original extensions directly. Binary quotient types and the exceptional
parabolic equivalences are excluded with their original weaker information.

This discharges the diagram branch conditionally on broad DGS markings for
every preparation. It assumes no final concrete comparison or two-core
identity. Exhaustiveness remains with qt-dgs85-source-assembly. The original
unitary extension restrictions for arbitrary selected R, the exchanged core
bound, prepared-U₅ recognition, uniqueness and GlobalExit assembly remain
with their existing owners and are not asserted here.

Source: Aschbacher--Smith 5.2.6, pp.650--651, F.1.12, pp.263--264, and the
literal Chapter 12 chosen-module setup, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual diagram source is impossible under the broad original marked
alternatives, before unitary outer collapse or whole-residual selection. -/
theorem rankOne_global_no_diagram_of_original_extensions
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
      (∃ (m : ℕ) (hm : 1 ≤ m) (point : Bool),
        Nonempty (Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H))) ∨
      (∃ (q : ℕ) (_ : IsPrimePow q) (_ : Even q)
        (M : ChapterF.GreenBook.UnitaryFive.Model q) (line : Bool)
        (_ : Function.Injective (MulAut.conj : M.Carrier →* MulAut M.Carrier)),
        Nonempty (Global.OriginalUnitaryFive.Marking M line L R (Global.sourceS L H))) ∨
      (∃ c : ChapterF.GreenBook.ExceptionalModels.Case,
        ChapterF.GreenBook.ExceptionalModels.ParabolicModel c
          (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∨
        ChapterF.GreenBook.ExceptionalModels.ParabolicModel c
          (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)).reverse) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL (![L,R] i ⧸ pCore 2 (![L,R] i)) 2 2) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i ⧸
          pCore 2 (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)) 2 2)) :
    ¬ Global.RightDiagramSource T L H := by
  intro hd
  obtain ⟨A,B,R,f,d,hp,_,hlin,hnot,hl,_⟩ :=
    D.rankOne_global_preparation_layers_of_diagram
      h hmany hn hpsl hH hpar hthree hN hunique hd
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have exclude := d.not_diagram_comparison hi hH.1.1.2 hN hp hlin hnot hl
  rcases hmark A B R d hp with hlinear | htri | hsymp | hree | hg2 | hfour | hfive | hexceptional | hlocal | hfull
  · obtain ⟨F,hfield,hfin,hchar,m,hm,hF,point,⟨e⟩⟩ := hlinear
    apply exclude
    exact D.rankOne_global_comparison_of_original_linear h hmany hn hpsl hH
      d hp F hm hF point e
  · obtain ⟨m,hm,a,⟨e⟩⟩ := htri
    apply exclude
    exact D.rankOne_global_comparison_of_original_triality h hmany hn hpsl hH
      d hp m hm a e
  · obtain ⟨F,hfield,hfin,hchar,m,hm,hF,point,⟨e⟩⟩ := hsymp
    apply exclude
    exact D.rankOne_global_comparison_of_original_symplectic h hmany hn hpsl hH
      d hp F hm hF point e
  · obtain ⟨m,a,⟨e⟩⟩ := hree
    apply exclude
    exact D.rankOne_global_comparison_of_original_ree h hmany hn hpsl hH
      d hp m a e
  · obtain ⟨F,hfield,hfin,hchar,short,⟨e⟩⟩ := hg2
    apply exclude
    exact D.rankOne_global_comparison_of_original_g2 h hmany hn hpsl hH
      d hp F short e
  · obtain ⟨m,hm,point,⟨e⟩⟩ := hfour
    exact d.not_original_unitaryFour_of_layer hi hH.1.1.2 hp hN hl m hm point e
  · obtain ⟨q,hq,heven,M,line,hfaithful,⟨e⟩⟩ := hfive
    exact d.not_original_unitaryFive_of_binary_right hi hH.1.1.2 hp hlin
      hq heven M line hfaithful e
  · obtain ⟨c,he⟩ := hexceptional
    have hc := d.not_exceptional_parabolic_models hi hp c
    exact he.elim hc.1 hc.2
  · obtain ⟨i,hi⟩ := hlocal
    exact d.not_binary_factor_quotient
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp i hi
  · obtain ⟨i,hi⟩ := hfull
    exact d.not_binary_parabolic_quotient
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hp i hi
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
