module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.FieldTransfer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# Ambient unitary-four transfer and Thompson counting for the chosen module

The original whole-reduced-module input discharges the assumptions of the
cyclic field-action transfer proof. Every ambient involution is fused into
T ∩ L, and exactly two ambient involution classes give Thompson's order
formula. Both comparison orientations, degree-two rows and q=4 remain.
The original sourceS is not identified with the reduced or ambient Sylow.

Source: Aschbacher--Smith F.4.35,38,43 and 5.3.3, printed pp.292,294,296,659,
with the original Chapter12 application on p.795 of `refs/quasithin.pdf`.
Comparison with the full marked extension's counts remains required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Global.UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}
variable (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (Global.sourceS L H) m hm)
include D h hmany hn hpsl hH d hp hm hc

/-- The literal matrix-field degree controls the reduced Sylow index. -/
theorem rankOne_unitaryFour_reduced_sylow_index_dvd :
    L.relIndex (T : Subgroup G) ∣ 2*m :=
  d.unitaryFour_reduced_sylow_index_dvd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc

/-- Every original ambient involution is fused into T ∩ L by generalized
Thompson transfer, including the degree-two comparison's graph involution. -/
theorem rankOne_unitaryFour_involution_fused_into_reduced_sylow
    (x : G) (hx : orderOf x = 2) :
    ∃ y ∈ (T : Subgroup G) ⊓ L, IsConj x y :=
  d.unitaryFour_involution_fused_into_reduced_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc x hx

/-- The actual ambient order formula has no coverage, nonfusion or parity
premise; the same-extension comparison of its terms remains to be proved. -/
theorem rankOne_unitaryFour_ambient_thompson_order :
    ∃ z ∈ L.pCoreIn 2, ∃ t ∈ L.pCoreIn 2,
      orderOf z = 2 ∧ orderOf t = 2 ∧ ¬ IsConj z t ∧
      (∀ x : G, orderOf x = 2 → IsConj x z ∨ IsConj x t) ∧
      Nat.card G = TwoInvolutionClassOrder.kappa z t z * Nat.card (centralizer ({t} : Set G)) +
        TwoInvolutionClassOrder.kappa z t t * Nat.card (centralizer ({z} : Set G)) :=
  d.unitaryFour_ambient_thompson_order
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
