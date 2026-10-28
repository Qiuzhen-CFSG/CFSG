module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearResidualComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityTerminal

/-!
# The odd-exponent Cartan on the chosen Chapter12 setup

Use the completed residual maximality and nonfaithfulness theorem and the
original whole-reduced input. The actual compatible left Cartan normalizes
the residual and acts trivially on its PSL₃(4) quotient. Its image in
H D_L/O₂(H D_L) is central, exactly as required by the parity seed.

No residual-geometry or Cartan-action premise remains in these applications.
The natural module, global TI setup and large-displacement theorem still
belong to qt-d-1222-linear-field-parity; parity is not asserted here.
Source: Aschbacher–Smith 5.1.17, printed pp.640–641, used in 12.2.2,
printed p.795 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The original odd-degree Cartan lies in the actual residual normalizer. -/
theorem rankOne_odd_cartan_normalizes_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n) :
    A ≤ normalizer (residual H : Set G) := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact cartan_normalizes_residual_of_odd hi hH c hodd hm hf

/-- The literal quotient-action kernel contains the actual odd-degree Cartan. -/
theorem rankOne_odd_cartan_residual_action_trivial
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n) :
    A ≤ ((normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker).map
      (normalizer (residual H : Set G)).subtype := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact cartan_residual_action_trivial_of_odd hi hH c hodd hm hf hlinear

/-- The central-image clause of the parity seed, with residual assertions discharged. -/
theorem rankOne_odd_cartan_image_central
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n) :
    (A.subgroupOf (H ⊔ A)).map (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))) ≤
      center ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact cartan_image_central_of_odd hi hH c hodd hm hf hlinear
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
