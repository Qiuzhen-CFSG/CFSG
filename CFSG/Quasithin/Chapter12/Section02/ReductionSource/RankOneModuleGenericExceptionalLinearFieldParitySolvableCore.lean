module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupCoreGeneration
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityNonabelian

/-!
# Solvable quotient-centralizer bounds on the chosen module

The source A.1.26(2) application is instantiated with the literal residual
quotient-action kernel and the chosen natural module. It controls the full
residual-normalizer orbit and the nonabelian core's Cartan layers. A prime
Cartan normalizer then proves generated-core containment and discharges the
earlier collapse premise. The Cartan centralizer in T is nontrivial
independently of solvability.

Solvability is precisely the remaining 5.1.16(2) input. The final parity
assembly, qt-d-1222-linear-field-parity, retains its discharge and the
residual-normalizer TI and abelian-span arguments.
Source: Aschbacher–Smith, 5.1.17, pp.640–641, used in 12.2.2, p.795
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The complete residual-normalizer orbit lies in its two-core. -/
theorem rankOne_odd_residual_normalizer_orbit_le_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    : conjugateSpanBy V (normalizer (residual H : Set G)) ≤
      (normalizer (residual H : Set G)).pCoreIn 2 := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_orbit_le_residual_normalizer_core hi hH c hodd hm hnf hlinear hsolv F hnat

/-- Both literal nonabelian Cartan layers lie in the point-normalizer core. -/
theorem rankOne_odd_nonabelian_cartan_layers_le_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L V).U)
    {l : G} (hl : l ∈ L) (hlout : l ∉ (normalizerSetup T L V).G₁) :
    let E := normalizerSetup T L V
    ⁅E.S l,A⁆ ⊔ E.S₂ l ≤ E.QH := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_nonabelian_cartan_layers_le_core hi hH c hodd hm hnf hlinear hsolv F hnat hnon hl hlout

/-- The actual Cartan has nontrivial fixed points in T. -/
theorem rankOne_odd_sylow_cartan_centralizer_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    : (T : Subgroup G) ⊓ centralizer (A : Set G) ≠ ⊥ := by
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact sylow_cartan_centralizer_ne_bot hi hH c hodd hm hnf hlinear

/-- The generated-core containment premise is discharged by solvability of the
literal quotient-centralizer; the original block-layer collapse follows. -/
theorem rankOne_odd_nonabelian_core_collapse_of_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L V).U)
    {l : G} (hl : l ∈ L) (hlout : l ∉ (normalizerSetup T L V).G₁) :
    let E := normalizerSetup T L V
    E.S l = E.S₂ l ∧ IsElementaryAbelian 2 (L.pCoreIn 2) ∧ ⁅L.pCoreIn 2,L⁆ = V := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  subst V
  exact fundamental_nonabelian_core_collapse_of_solvable hi hH c hodd hm hnf hlinear hsolv F hnat hnon hl hlout

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
