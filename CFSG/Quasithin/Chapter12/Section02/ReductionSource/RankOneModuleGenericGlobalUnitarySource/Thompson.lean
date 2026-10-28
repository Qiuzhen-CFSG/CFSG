module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Thompson
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource

/-!
# Inner Thompson control for the original whole reduced module

The original chosen-module hypotheses and the actual compatible unitary
comparison give J(T ∩ L)=O₂(L), its unique maximum elementary subgroup,
and ambient weak closure inside that reduced Sylow. This is the inner
calculation for F.4.35 (printed p.292), applied to the literal Chapter12
module without replacing the full KnownSimple catalogue or the source Sylow.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original residual embedding gives the exact inner Thompson subgroup. -/
theorem rankOne_unitary_inner_thompson
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ L) = L.pCoreIn 2 := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_inner_thompson hi hH hp m hm hc

/-- Every largest elementary subgroup of the reduced common Sylow is the
literal O₂(L). -/
theorem rankOne_unitary_inner_unique_maximum
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    (E : Subgroup G)
    (hE : E ∈ elementaryAbelianMaxSubgroups ((T : Subgroup G) ⊓ L)) :
    E = L.pCoreIn 2 := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_inner_unique_maximum hi hH hp m hm hc E hE

/-- Weak closure under G-conjugation in T ∩ L, with T retained separately. -/
theorem rankOne_unitary_inner_core_weakly_closed
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    (g : G) (hg : (L.pCoreIn 2).conjBy g ≤ (T : Subgroup G) ⊓ L) :
    (L.pCoreIn 2).conjBy g = L.pCoreIn 2 := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_inner_core_weakly_closed hi hH hp m hm hc g hg

/-- Normalizing the inner Thompson subgroup is exactly normalizing the
original left residual; no smaller parabolic replaces the full normalizer. -/
theorem rankOne_unitary_inner_thompson_normalizer
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
    : normalizer (elementaryAbelianMaxJ ((T : Subgroup G) ⊓ L) : Set G) =
      normalizer (L : Set G) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_inner_thompson_normalizer hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
