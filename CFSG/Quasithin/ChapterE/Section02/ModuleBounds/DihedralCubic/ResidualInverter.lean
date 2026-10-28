module

public import Theory.GroupAction.OddInvolutionFrattini.Quotient
public import CFSG.Quasithin.ChapterB.Section06To07.NormalActor
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.ResidualNineFrattini

/-!
# The source residual Frattini inverter

In a solvable minimal parabolic, a Sylow-normal elementary two-subgroup V
whose image modulo O₂(H) has order two generates O²(H) by commutators.
B.6.8 identifies the residual image as a p-group for an odd prime p. The commutator
argument therefore supplies an actual v ∈ V inverting
O²(H)/(O²(H) ∩ O₂(H)) modulo Frattini. This removes the inversion premise
from the residual-nine obstruction for the literal quaternion action.

The order-two image is the small-core witness input, supplied independently
in the E.2.17 source assembly. Neither commutator generation, quotient
prime-group structure, nor inversion is assumed here.

Source: Aschbacher--Smith, E.2.17, printed pp.229--230.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.DihedralCubic

/-- The original solvable local data supply the literal Frattini inverter. -/
theorem source_residual_frattini_inverter
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : Group.IsSolvable H)
    (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hn : (V.subgroupOf (S : Subgroup H)).Normal)
    (hV : Nat.card (V.map (QuotientGroup.mk' (pCore 2 H))) = 2) :
    ∃ v ∈ V, ∀ k : pResidual 2 H,
      (MulAut.conjNormal v : MulAut (pResidual 2 H)) k * k ∈
      (frattini (pResidual 2 H ⧸ (pCore 2 H).subgroupOf (pResidual 2 H))).comap
        (QuotientGroup.mk' ((pCore 2 H).subgroupOf (pResidual 2 H))) := by
  have hout : ¬ V ≤ pCore 2 H := by
    intro hle
    have hz : V.map (QuotientGroup.mk' (pCore 2 H)) = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      simpa only [QuotientGroup.ker_mk'] using hle
    rw [hz, card_bot] at hV
    norm_num at hV
  have hcomm := ChapterB.minimalParabolic_residual_commutator_of_normalized_two_actor
    S hP V hVS ((normal_subgroupOf_iff_le_normalizer hVS).mp hn) hout
  obtain ⟨p,hp,_,hres,_⟩ := ChapterB.minimalParabolic_solvable_structure S hP hs
  let : Fact p.Prime := ⟨hp⟩
  apply OddInvolutionFrattini.exists_frattini_inverter (p := p) (pResidual 2 H) (pCore 2 H) V hcomm hV
  rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),hres]
  exact pCore_isPGroup

/-- The source order-nine exclusion with its inverter constructed from the local data. -/
theorem source_residual_image_ne_nine_of_two_actor_image
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : Group.IsSolvable H)
    (U V : Subgroup H) [U.Normal] [IsElementaryAbelian 2 V]
    (d : QuaternionCentralProductData U)
    (hVS : V ≤ S) (hn : (V.subgroupOf (S : Subgroup H)).Normal)
    (hV : Nat.card (V.map (QuotientGroup.mk' (pCore 2 H))) = 2) :
    Nat.card ((pResidual 2 H).map (d.quotientWreathAction.comp MulAut.conjNormal)) ≠ 9 := by
  obtain ⟨v,hv,hi⟩ := source_residual_frattini_inverter S hP hs V hVS hn hV
  exact source_residual_image_ne_nine_of_frattini_inversion
    S U V d hVS hn v hv hi

end CFSG.Quasithin.ChapterE.DihedralCubic
