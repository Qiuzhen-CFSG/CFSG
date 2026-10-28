module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# Full common-normalizer actions for the original unitary rows

The literal whole-reduced-module input constructs faithful marked-pair
conjugation actions of N_G(L) ∩ N_G(O²(H)) for the ordinary and degree-two
U₄ comparisons and for U₅(4), in both orientations. The same action identifies
the preimage of the native Borel-inner action with the complete reduced
overlap. In the degree-two row the original graph involution survives as
an involution outside this inner action range. The original ambient T,
sourceS and T ∩ L retain their distinct meanings.

Source: Aschbacher–Smith 5.3.1–2 and F.4.37, printed pp.658–659,293,
with the Chapter12 application on p.795 of `refs/quasithin.pdf`.
Extending the marked action to automorphisms of the concrete unitary group,
ambient outer transfer, F.4.42 and the order bound remain to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original chosen module supplies this marked source conclusion. -/
theorem rankOne_unitary_native_middle_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
      (Nonempty (UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
        (amalgam m hm)) ∨
       Nonempty (UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
        (amalgam m hm).reverse)) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_native_middle_action hi hH hp m hm hc

/-- The original chosen module supplies this marked source conclusion. -/
theorem rankOne_unitary_reduced_overlap_sylow
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    (T : Subgroup G) ⊓ (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 : Subgroup G) =
      (T : Subgroup G) ⊓ L := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_reduced_overlap_sylow hi hH hp m hm hc

/-- The original chosen module supplies this marked source conclusion. -/
theorem rankOne_unitaryFive_native_middle_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    Nonempty (UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam) ∨
    Nonempty (UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_native_middle_action hi hH hp U hc

/-- The original chosen module supplies this marked source conclusion. -/
theorem rankOne_unitary_graph_native_middle_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧ ∃ f : G,
      f ∈ sourceS L H ∧ f ∈ (T : Subgroup G) ∧ orderOf f = 2 ∧
      f ∉ L ∧ f ∉ residual H ∧
      ∃ hf : f ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G),
        (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
            (amalgam m hm),
          orderOf (a.action ⟨f,hf⟩) = 2 ∧
          a.action ⟨f,hf⟩ ∉ (UnitarySource.innerMiddle (amalgam m hm)).range) ∨
        (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
            (amalgam m hm).reverse,
          orderOf (a.action ⟨f,hf⟩) = 2 ∧
          a.action ⟨f,hf⟩ ∉ (UnitarySource.innerMiddle (amalgam m hm).reverse).range) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_graph_native_middle_action hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
