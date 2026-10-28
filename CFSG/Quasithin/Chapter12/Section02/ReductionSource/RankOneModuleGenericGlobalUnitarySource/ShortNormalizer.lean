module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.ShortRoot

/-!
# The chosen module's full-normalizer short-root three-space

For the literal whole-reduced chosen module, the long-root normal closure
in X=C_{N_G(L)}(t) is the intrinsic subgroup [O₂(L),C_L(t)] of order q³.
Its central part relative to C_L(t) is a q-element line normalized by X.
All subgroups and relative normal closures use the original ambient G.
Both ordinary and degree-two comparisons, either orientation and q=4
are retained with m>1 and n=2m.

Source: Aschbacher–Smith F.4.42 and its 5.3/12.2 application, printed
pp.295–296,659,795 of `refs/quasithin.pdf`. The ambient unique-fixed-coset
argument and the full-residual fixed-line identification remain further
steps of the source centralizer-containment proof.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original chosen module constructs the full-normalizer long-root
normal closure and its invariant local fixed line. -/
theorem rankOne_unitary_short_root_normalizer_module
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
      let Y := L ⊓ centralizer ({t.val} : Set G)
      let X := normalizer (L : Set G) ⊓ centralizer ({t.val} : Set G)
      let V := ⁅L.pCoreIn 2,Y⁆
      let U := V ⊓ centralizer (Y : Set G)
      IsElementaryAbelian 2 V ∧ V ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ U.relIndex V = (2^m)^2 ∧
      zpowers t.val < U ∧ X ≤ normalizer (V : Set G) ∧ X ≤ normalizer (U : Set G) ∧
      ∃ z : X, orderOf z.val = 2 ∧
        (normalClosure ({z} : Set X)).map X.subtype = V := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_root_normalizer_module hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
