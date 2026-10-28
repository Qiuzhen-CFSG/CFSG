module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The original chosen module and unique long-root quotient lifts

Apply the prepared calculation with W equal to the original whole reduced
module. The same marked roots give the q²−1 local orbit, its centralizing
Sylow, unique long-root lifts, and the exact quotient centralizer preimage.
Both orientations, ordinary and degree-two rows, q=4, and the full kernel
are retained. Ambient unique fixed cosets and order comparison remain open.
Source: Aschbacher–Smith F.4.42 and 5.3/12.2, pp.295–296,659,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The literal Chapter12 row supplies the original-root orbit and exact
full-line quotient lifts without additional local or fusion assumptions. -/
theorem rankOne_unitary_short_quotient_long_lifts
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
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
      centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
        normalizer (L : Set G) ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      U ≤ V ∧ IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧
      Nat.card {x : centralizer ({t} : Set L) // IsConj z x} = (2^m)^2 - 1 ∧
      (∃ P : Sylow 2 (centralizer ({t} : Set L)),
        (P : Subgroup _) ≤ centralizer ({z} : Set _)) ∧
      (∀ v ∈ V.map f, v ≠ 1 →
        ∃! x : centralizer ({t} : Set L), IsConj z x ∧ f x = v) ∧
      (centralizer ({f z} : Set _)).comap f = centralizer ({z} : Set _) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitary_short_quotient_long_lifts hi hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
