module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Module
public import Theory.GroupAction.PPerfectFixedCentralizer
public import Theory.GroupTheory.Gaschutz

/-!
# The parabolic Sylow interface for the natural-extension endgame

The source's second paragraph has two separate inputs.  The first is the
literal nonsplit four-dimensional natural-extension calculation (B.4.8(3));
the second is the coprime-action lift from the quotient by `V₁`.  This module
records the actual Sylow placement and proves the group-theoretic lifting
lemma used after the B.4.8 calculation.  The B.4.8 input is kept at its
published interface; no conclusion-shaped centralizer hypothesis is hidden
here.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.7.74, printed p.1077 (PDF p.1094), and A.4.8(5).
-/

@[expose] public section
noncomputable section

open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (a : Prior d)

include d a

omit a in
/-- The canonical `QC U` lies in the actual point normalizer `H`.

The `QC` part lies in the ambient Sylow subgroup and therefore normalizes
the point of the invariant flag; the `U` part lies in `H` by construction.
This is the containment needed before applying the original `H`-action to
the four-dimensional extension.
-/
theorem QCU_le_H : QC T L V ⊔ F.U ≤ F.H := by
  have hQT : Q T L ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hVU : V ≤ F.U := Data.V_le_U F
  have hVcenter : V ≤ centralizer (F.U : Set G) :=
    hVU.trans (le_centralizer_iff_isMulCommutative.mpr d.abelian)
  have hVH : V ≤ F.H :=
    (hVcenter.trans (centralizer_le ((F.le_seed 1).trans hVU))).trans
      (Subgroup.centralizer_le_normalizer _)
  apply sup_le
  · exact (commutatorPreimage_le _ _ _).trans (hQT.trans (F.invariant 1))
  · exact conjugateSpanBy_le_self hVH

/-- The two-core supplied by `Prior` is the actual Sylow two-subgroup used in
the second Gaschütz/coprime-action paragraph. -/
theorem parabolic_core_eq : (F.Li L 1).pCoreIn 2 = S L F ⊔ (K F).pCoreIn 2 :=
  a.parabolic_core

theorem parabolic_core_sylow :
    Chapter1.IsSylowIn 2 ((F.Li L 1).pCoreIn 2) (K F) := by
  rw [parabolic_core_eq d a]
  exact a.parabolic_sylow

omit d a [Finite G] [AddCommGroup W] [Module (ZMod 2) W] in
/-- Every element of the parabolic two-core centralizes the literal `QL`.

This is the concrete fixed Sylow required by the coprime-action lift: the
core is contained in `L₁ ≤ L`, while `QL` is defined as the subgroup of `Q`
centralizing `L`.
-/
theorem parabolic_core_centralizes_QL :
    (F.Li L 1).pCoreIn 2 ≤ centralizer (QL T L : Set G) := by
  intro x hx y hy
  have hxL : x ∈ L :=
    (pCoreIn_le 2 (F.Li L 1)).trans ((F.Li_le L 1).trans inf_le_left) hx
  exact (mem_centralizer_iff.mp
    (show y ∈ centralizer (L : Set G) from (show QL T L ≤ centralizer (L : Set G)
      from inf_le_right) hy) x hxL).symm

omit d a [AddCommGroup W] [Module (ZMod 2) W] in
/-- A quotient-level coprime-action lift in the exact form used by 14.7.74.

The subgroup `Z` is the actual elementary abelian quotient supplied by the
nonsplit natural-extension calculation.  The theorem uses the genuine
two-perfect actor and its actual Sylow two-subgroup; the proof is the
fixed-point `P × Q` argument, so no centralization conclusion is assumed.
-/
theorem coprime_action_lift
    (E Q Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hE : IsPPerfect 2 E) (hQ : IsPGroup 2 Q)
    (hEN : E ≤ normalizer (Z : Set G))
    (hQN : Q ≤ normalizer (Z : Set G))
    (hcomm : ⁅Q, E⁆ ≤ centralizer (Z : Set G))
    (hfix : ⁅Z ⊓ centralizer (Q : Set G), E⁆ = ⊥) :
    ⁅Z, E⁆ = ⊥ :=
  IsPPerfect.centralizes_of_commuting_fixed E Q Z hE hQ hEN hQN hcomm hfix

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity
