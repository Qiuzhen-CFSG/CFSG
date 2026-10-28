module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNormalJankoField
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The chosen-module application of the normal J₁ field action

Apply the normal J₁ field calculation to the literal original chosen-module
input. The original right Hall subgroup acts faithfully, with field image
of order three, on the actual left two-core quotient. No additional action
or movement hypothesis is introduced. The normal J₁ row still requires the
omega movement and faithful local-component argument.
Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.637,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The original right cubic has its actual faithful field action. -/
theorem rankOne_local_cartan_normalJanko_cubic_field_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hRC : (residual H).subgroupOf Y ≤ C)
    (eC : (C ⧸ pCore 2 C) ≃* Janko1.Model)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,F)) :
    let a := (MulAut.congr e).toMonoidHom.comp
      ((normalizerQuotientAction L (pCore 2 L)).comp
        (inclusion (c.right_le.trans inf_le_left)))
    let f := (Theory.PSL2.fieldProjection F).comp a
    Function.Injective f ∧ Nat.card f.range = 3 :=
  LocalSieve.normal_janko_cubic_field_action
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape C hRC eC e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
