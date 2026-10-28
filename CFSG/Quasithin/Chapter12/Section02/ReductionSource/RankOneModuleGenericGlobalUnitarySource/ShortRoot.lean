module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortRoot
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The chosen-module unitary short-root three-space and fixed line

The original whole-reduced module constructs short and long involutions in
L. In C_L(t), the normal closure of the long involution is elementary
abelian of order q³ and lies in the original O₂(L). Its fixed subgroup under
O^{2′}(C_L(t)) is the q-element short-root line, of index q² in that
three-space, and strictly contains the marked involution. The entire line
is central in C_L(t). All maps pass through the actual projectivization;
both ordinary and degree-two comparisons and both orientations retain q=4.

Source: Aschbacher–Smith F.4.42 and its 5.3/12.2 application, printed
pp.295–296,659,795 of `refs/quasithin.pdf`. The ambient unique-fixed-coset,
normalizer and short-root centralizer-containment arguments remain further
obligations. This theorem concerns the literal residual centralizer C_L(t).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The literal whole-reduced chosen module supplies the local orthogonal
three-space, its long-root generator and its full short-root fixed line. -/
theorem rankOne_unitary_short_root_module
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
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ U.relIndex V = (2^m)^2 ∧
      U ≤ V ∧ U ≤ center (centralizer ({t} : Set L)) ∧
      V ⊓ centralizer (primeToResidual 2 (centralizer ({t} : Set L)) :
        Set (centralizer ({t} : Set L))) = U ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_root_module hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
