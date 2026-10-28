module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFive
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalG2Extension
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFiveSource.Completion

/-!
# Original U₅ extension collapse at the Chapter 12 consumer

The broad original marking, for any field and orientation, yields a concrete
U₅(4) comparison for every selected perfect R. The same maps restrict through
the full overlap. A universal broad marking premise therefore feeds the
literal residual preparation. Once R is the residual, the already proved
prepared U₅ completion supplies GlobalExit without a core, field-action,
extension-order or pure-comparison callback.

The broad markings and their exhaustiveness remain inputs of the DGS source
assembly. The surviving original U₄ extension and unconditional uniqueness
and GlobalExit assembly remain separate obligations.
Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6, pp.650--651,
and Chapter 12, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Original extension reduction precedes identification of the selected R. -/
theorem rankOne_global_comparison_of_original_unitaryFive
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    (M : ChapterF.GreenBook.UnitaryFive.Model q) (line : Bool)
    (hi : Function.Injective (MulAut.conj : M.Carrier →* MulAut M.Carrier))
    (e : Global.OriginalUnitaryFive.Marking M line L R (Global.sourceS L H)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.concreteComparison_of_original_unitaryFive
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hq heven M line hi e

/-- The actual Chapter 12 S lies in both marked factors and changes neither core. -/
theorem rankOne_global_original_unitaryFive_collapse
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (M : ChapterF.GreenBook.UnitaryFive.Model 4)
    (e : Global.OriginalUnitaryFive.Marking M false L R (Global.sourceS L H)) :
    Global.sourceS L H ≤ R ∧ Global.sourceS L H ≤ L ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧
      (L ⊔ Global.sourceS L H).pCoreIn 2 = L.pCoreIn 2 := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hs := d.original_unitaryFive_sourceS_le hi hH.1.1.2 hp M e
  exact ⟨hs.1,hs.2,d.original_unitaryFive_core_eq hi hH.1.1.2 hp M e⟩

/-- A broad original U₅ marking on the residual gives the existing prepared
completion and the actual strict-exponent GlobalExit. -/
theorem rankOne_globalExit_of_original_unitaryFive
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    (M : ChapterF.GreenBook.UnitaryFive.Model q) (line : Bool)
    (hi : Function.Injective (MulAut.conj : M.Carrier →* MulAut M.Carrier))
    (e : Global.OriginalUnitaryFive.Marking M line L (residual H) (Global.sourceS L H)) :
    RankOneModule.GlobalExit G := by
  let hi' := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hq4 := Global.Preparation.original_unitaryFive_marked_field hi' hq heven M line hi e
  subst q
  have ho := d.original_unitaryFive_marked_orientation hi' hH.1.1.2 hp M line e
  subst line
  exact D.rankOne_globalExit_of_unitaryFive_source h hmany hn hpsl hH d hp M
    (Or.inr ⟨d.originalUnitaryFiveComparison hi' hH.1.1.2 hp M e⟩)

/-- Six original regular families feed the same selected-factor residual
preparation. Broad marked data remain explicit, including arbitrary U₅ fields
and orientations and the general Ree family; no pure comparison is assumed. -/
theorem rankOne_global_residual_preparation_of_original_regular_extensions
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
      (∃ (q : ℕ) (_ : IsPrimePow q) (_ : Even q)
        (M : ChapterF.GreenBook.UnitaryFive.Model q) (line : Bool)
        (_ : Function.Injective (MulAut.conj : M.Carrier →* MulAut M.Carrier)),
        Nonempty (Global.OriginalUnitaryFive.Marking M line L R (Global.sourceS L H))) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL (![L,R] i ⧸ pCore 2 (![L,R] i)) 2 2) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i ⧸
          pCore 2 (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)) 2 2)) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Group.IsPerfect (residual H) := by
  apply D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique
  intro A B R d hp
  rcases hmark A B R d hp with hlin | htri | hsymp | hree | hg2 | hunitary | hlocal | hfull
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
  · obtain ⟨q,hq,heven,M,line,hi,⟨e⟩⟩ := hunitary
    exact D.rankOne_global_comparison_of_original_unitaryFive
      h hmany hn hpsl hH d hp hq heven M line hi e
  · obtain ⟨i,hi⟩ := hlocal
    exact False.elim (d.not_binary_factor_quotient
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp i hi)
  · obtain ⟨i,hi⟩ := hfull
    exact False.elim (d.not_binary_parabolic_quotient
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hp i hi)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
