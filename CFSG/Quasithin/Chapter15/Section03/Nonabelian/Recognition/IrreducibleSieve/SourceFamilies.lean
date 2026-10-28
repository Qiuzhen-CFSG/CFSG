module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Common
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.RankOne
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.BinaryLinear
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.OddAndSporadic
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.RankTwo
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.TwoFactors

/-!
# Complete simple-model exclusion for the source irreducible branch

The source action excludes every model in the proved Theorem C catalogue.
All branches use the original elementary actor, Sylow subgroup, quadratic
form and marked involution. The classifications in defining characteristic
are applied only at the degree bound already supplied by those hypotheses.

Source: Aschbacher--Smith, G.9.3 and the irreducible branch of 15.3.58,
printed pp.354--357 and 1149.
-/

public section

open Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterG.Section09

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- Every simple component model is excluded by the original marked source action. -/
theorem not_simple_component (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (hc : ComponentHypothesis KnownSimple.IsKnownSimple ρ X K K (s + 1))
    (hq : IsSQTK KnownSimple.IsKnownSimple H)
    (hs : IsSimpleGroup K) (hn : ¬ IsMulCommutative K)
    (hm : ChapterA.Section02.IsTheoremCModel K) : False := by
  cases hm with
  | alternating n hn' he =>
    exact OddAndSporadic.exclude_alternating h hK hs hn n hn' he
  | odd hm => exact OddAndSporadic.exclude_odd h hK hs hn hm
  | bender hm =>
    cases hm with
    | linear n hn' he => exact h.not_binary_rankOne_model hK n hn' he
    | unitary n hn' he => exact h.not_unitaryThree_component hK hn' he
    | suzuki n hn' he => exact h.not_suzuki_component hK hn' he
  | rank_two f hm => exact h.not_rankTwo_component hK hq hs hn hm
  | linear_binary n hn' he => exact h.not_binary_linear_model hK hc n hn' he
  | sporadic hm => exact OddAndSporadic.exclude_sporadic h hK hs hn hm

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies
