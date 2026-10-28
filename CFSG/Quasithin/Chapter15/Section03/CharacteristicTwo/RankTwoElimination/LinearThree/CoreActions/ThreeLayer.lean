module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Layers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Frattini
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Moving
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Displacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.ResidualAlternatives
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic

/-!
# Core control in the compatible third C.1.34 alternative

The natural center is fixed by Y_C and is not fixed by Y_L. The actual
intersection of the residual two-cores gives the moving-case contradiction:
its two displacement subgroups equal Q, so exchange would preserve Q and its
center, contradicting the different actual center actions. Neither an
intersection equality nor conjugation invariance of Q is an input.

The plane-parabolic calculation proves [Q,Y_L] = Q on the actual doubled-dual
quotient and lifts through Z(Q) ≤ Φ(Q). The commuting action of the genuine
two-perfect residual Y_C supplies the fixed-or-moving alternative, so the
moving-case contradiction proves that Y_C fixes Q. Two-perfectness then
gives centralization of L and the required bound on Qᵗ. No full-order-three
or coprime-action assumption on Y_C is used.

`core_actions` discharges both action premises of the earlier conditional
exports. `core_actions_of_source_geometry` uses the preceding conclusions
S ≤ N_G(L) and Y₊ = Y to obtain residual normalization. The common marking,
both literal layers, the order-four fixed subgroup and its parabolic remain
explicit source inputs; constructing the MS-pair, obtaining its third
alternative and completing the other cases of 15.3.23 belong to their owners.

Source: Aschbacher–Smith, C.1.34(3), printed pp.136–137, and the k = 3
paragraph of 15.3.23, printed p.1129 (combined manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
variable {G : Type*} [Group G] [Finite G]

/-- Eliminate the moving branch using the actual center action and common-core displacement. -/
theorem YC_fixes_core_of_action_alternatives (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel c.L (coreCenter c.L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hU : ⁅d.V, YL d c.L⁆ ≠ ⊥)
    (hUZ : ⁅d.V, YL d c.L⁆ ≤ coreCenter c.L)
    (hfixU : YC d c.L ≤ centralizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (hfullL : ⁅commutatorCore c.L, YL d c.L⁆ = commutatorCore c.L)
    (halternatives : YC d c.L ≤ centralizer (commutatorCore c.L : Set G) ∨
      ⁅commutatorCore c.L, YC d c.L⁆ = commutatorCore c.L)
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hex : (YL d c.L).conjBy t = YC d c.L) :
    YC d c.L ≤ centralizer (commutatorCore c.L : Set G) := by
  rcases halternatives with hfix | hmove
  · exact hfix
  · exact (not_both_moving d c m hindex hcore hR hSYL hU hUZ hfixU hfullL t ht hex hmove).elim

/-- The source conjugate-core bound once the two action calculations are supplied. -/
theorem conjugate_core_centralizes_of_action_alternatives (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel c.L (coreCenter c.L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hU : ⁅d.V, YL d c.L⁆ ≠ ⊥)
    (hUZ : ⁅d.V, YL d c.L⁆ ≤ coreCenter c.L)
    (hfixU : YC d c.L ≤ centralizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (hfullL : ⁅commutatorCore c.L, YL d c.L⁆ = commutatorCore c.L)
    (halternatives : YC d c.L ≤ centralizer (commutatorCore c.L : Set G) ∨
      ⁅commutatorCore c.L, YC d c.L⁆ = commutatorCore c.L)
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hex : (YL d c.L).conjBy t = YC d c.L) :
    (commutatorCore c.L).conjBy t ≤ centralizer (c.L : Set G) :=
  conjugate_core_centralizes_of_full_action d c (commutatorCore_le_S d c.L hcore hR)
    hSYL hfullL (YC_fixes_core_of_action_alternatives d c m hindex hcore hR hSYL
      hU hUZ hfixU hfullL halternatives t ht hex) t hex

/-- The two required core actions in the third C.1.34 case. Both quotient
calculations and the exclusion of the moving alternative are proved here;
only the preceding local and fixed-plane geometry is supplied. -/
theorem core_actions (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel c.L (coreCenter c.L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (n : LayerModel c.L (commutatorCore c.L) (coreCenter c.L) e (DualCopies (ZMod 2) 2))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hU : Nat.card (⁅d.V, YL d c.L⁆ : Subgroup G) = 4)
    (hUZ : ⁅d.V, YL d c.L⁆ ≤ coreCenter c.L)
    (hfixU : YC d c.L ≤ centralizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (hpar : YL d c.L ⊔ (d.S ⊓ c.L) =
      c.L ⊓ normalizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hex : (YL d c.L).conjBy t = YC d c.L) :
    ⁅commutatorCore c.L, YL d c.L⁆ = commutatorCore c.L ∧
      YC d c.L ≤ centralizer (commutatorCore c.L : Set G) := by
  have hU_ne : ⁅d.V, YL d c.L⁆ ≠ ⊥ := by
    intro hbot
    norm_num [hbot, Subgroup.card_bot] at hU
  have hfull := YL_full_displacement d c.L m n hSYL hU hUZ hpar
  have hcenter := YC_fixes_center d c.L m hcore hR
    (S_normalizes_YC d c.L hindex hSYL t ht hex) hUZ hU_ne hfixU
  exact ⟨hfull, YC_fixes_core_of_action_alternatives d c m hindex hcore hR hSYL
    hU_ne hUZ hfixU hfull (YC_fixed_or_moving d c m n hcenter) t ht hex⟩

/-- Source-facing form of the action theorem: normalization of Y_L follows
from S ≤ N_G(L), Y₊ = Y, and the actual normal residual Y in M. The result
allows every order-four plane in the supplied natural marking. -/
theorem core_actions_of_source_geometry (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel c.L (coreCenter c.L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (n : LayerModel c.L (commutatorCore c.L) (coreCenter c.L) e (DualCopies (ZMod 2) 2))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (hY : d.Yplus = d.Y)
    (hU : Nat.card (⁅d.V, YL d c.L⁆ : Subgroup G) = 4)
    (hUZ : ⁅d.V, YL d c.L⁆ ≤ coreCenter c.L)
    (hfixU : YC d c.L ≤ centralizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (hpar : YL d c.L ⊔ (d.S ⊓ c.L) =
      c.L ⊓ normalizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hex : (YL d c.L).conjBy t = YC d c.L) :
    ⁅commutatorCore c.L, YL d c.L⁆ = commutatorCore c.L ∧
      YC d c.L ≤ centralizer (commutatorCore c.L : Set G) := by
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)).mp
        (residualY_normal d.M d.Mc)
  have hSY : d.S ≤ normalizer (d.Yplus : Set G) := by
    rw [hY]
    exact (inf_le_left.trans d.sylow_le).trans hMY
  exact core_actions d c m n hindex hcore hR (S_normalizes_YL d c.L hSY hSL)
    hU hUZ hfixU hpar t ht hex

/-- The three-layer conjugate-core bound with both action premises discharged. -/
theorem conjugate_core_centralizes (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel c.L (coreCenter c.L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (n : LayerModel c.L (commutatorCore c.L) (coreCenter c.L) e (DualCopies (ZMod 2) 2))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSYL : d.S ≤ normalizer (YL d c.L : Set G))
    (hU : Nat.card (⁅d.V, YL d c.L⁆ : Subgroup G) = 4)
    (hUZ : ⁅d.V, YL d c.L⁆ ≤ coreCenter c.L)
    (hfixU : YC d c.L ≤ centralizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (hpar : YL d c.L ⊔ (d.S ⊓ c.L) =
      c.L ⊓ normalizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hex : (YL d c.L).conjBy t = YC d c.L) :
    (commutatorCore c.L).conjBy t ≤ centralizer (c.L : Set G) := by
  obtain ⟨hfull, hfix⟩ := core_actions d c m n hindex hcore hR hSYL
    hU hUZ hfixU hpar t ht hex
  exact conjugate_core_centralizes_of_full_action d c
    (commutatorCore_le_S d c.L hcore hR) hSYL hfull hfix t hex

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
end
