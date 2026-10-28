module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Module

/-!
# Natural-extension rigidity: checked module reductions

The canonical QC is elementary abelian after C_Q(L) vanishes, and its
actual quotient by V embeds into the natural first cohomology for the
same qL marking. Thus QC has order at most sixteen. The final theorem
below consumes Ambient's genuine unique maximal two-local argument to
supply that vanishing from K-centralization.

The centralizer comparison, second Gaschütz application and coprime-action
step establishing K-centralization remain open. The displacement by O₂(L₁)
in the proper-extension case also remains open; Module supplies its
literal linear-to-group consumer. These reductions are not the completed
source theorem. Final natural-rigidity assembly remains in this module,
and complete 14.7.74 assembly belongs to LocalCollapse.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.7.74, printed p.1077 (PDF p.1094).
-/

@[expose] public section

open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (a : Prior d)

variable (hKC : ⁅QC T L V, K F⁆ ≤ F.U)

include a hKC in
/-- The Frattini and cohomology arguments give the actual group a bound of sixteen. -/
theorem QC_elementary_and_card_le (hQL : QL T L = ⊥) :
    IsElementaryAbelian 2 (QC T L V) ∧ Nat.card (QC T L V) ≤ 16 := by
  let := QC_elementary d a hQL
  refine ⟨inferInstance, ?_⟩
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (QC T L V))
  change Nat.card (QC T L V) = _ at hc
  rw [hc, Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (QC_finrank_le_four d a hKC hQL))

include a hKC in
theorem QC_frattini_and_card_of_K_centralizes
    (hKQL : K F ≤ centralizer (QL T L : Set G)) :
    frattini (QC T L V) = ⊥ ∧ Nat.card (QC T L V) ≤ 16 := by
  have hQL := QL_eq_bot_of_K_centralizes d a hKQL
  exact ⟨QC_frattini d a hQL, (QC_elementary_and_card_le d a hKC hQL).2⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity
