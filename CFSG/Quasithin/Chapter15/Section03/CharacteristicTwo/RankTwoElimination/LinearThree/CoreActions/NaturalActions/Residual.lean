module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.Multiplicity
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.Coordinates

/-!
# The natural-layer residual centralizes the actual commutator core

The transported residual action commutes with the natural SL₃(2) action.
A nonidentity element of a fixed subgroup of Q gives a common nonzero fixed
vector, so the multiplicity calculation kills this two-perfect action. The
existing residual lifting theorem then gives centralization of L. The source
adapter uses the actual order-four subgroup [V,Y_L], with either coordinate
orientation; it never treats Y_C as a group of order three.

Source: Aschbacher–Smith, proof of 15.3.23, final paragraph of printed p.1129,
using C.1.34(1),(2), printed pp.136–137.
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial subgroup of the natural core fixed by the actual two-residual
forces that residual to centralize the whole core. -/
theorem YC_centralizes_natural_core (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) {a : ℕ} (ha : a = 1 ∨ a = 2)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Actor}
    (m : LayerModel c.L (commutatorCore c.L) ⊥ e (NaturalCopies (ZMod 2) a))
    (U : Subgroup G) (hU : U ≠ ⊥) (hUQ : U ≤ commutatorCore c.L)
    (hfix : YC d c.L ≤ centralizer (U : Set G)) :
    YC d c.L ≤ centralizer (commutatorCore c.L : Set G) := by
  obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  let q : commutatorCore c.L := ⟨u, hUQ u.property⟩
  let w := Multiplicative.toAdd (m.upperIso q)
  have hw : w ≠ 0 := by
    intro h
    have he : m.upperIso q = 1 := congrArg Multiplicative.ofAdd h
    have hq := m.upperIso.injective (he.trans m.upperIso.map_one.symm)
    exact hu (Subtype.ext (congrArg (fun z : commutatorCore c.L => (z : G)) hq))
  have hfw (y : YC d c.L) : residualAction c m y w = w := by
    rw [residualAction, coordinateAction_apply]
    have he : layerConjugate (YC d c.L) (commutatorCore c.L)
        ((YC_section_action d c.L).1.trans (normalizer_le_normalizer_commutatorCore c.L)) y q = q := by
      apply Subtype.ext
      change (y : G) * (u : G) * (y : G)⁻¹ = u
      rw [← hfix y.property u u.property, mul_inv_cancel_right]
    rw [he]
  have ht := twoPerfect_copies_fixed ha (residualAction c m)
    (ComponentIntersection.centralizerResidual_isPPerfect d.Yplus c.L)
    (residualAction_commutes c m) w hw hfw
  intro y hy x hx
  have he := LinearMap.congr_fun (ht ⟨y, hy⟩) (Multiplicative.toAdd (m.upperIso ⟨x,hx⟩))
  rw [residualAction, coordinateAction_apply] at he
  have hq := m.upperIso.injective (congrArg Multiplicative.ofAdd he)
  have hval := congrArg Subtype.val hq
  change y * x * y⁻¹ = x at hval
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm

/-- The fixed-space output in 15.3.23 uses an actual subgroup of order four.
Only its nontriviality and pointwise fixation are needed at this step. -/
theorem YC_centralizes_of_order_four (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) {a : ℕ} (ha : a = 1 ∨ a = 2)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Actor}
    (m : LayerModel c.L (commutatorCore c.L) ⊥ e (NaturalCopies (ZMod 2) a))
    (hU : Nat.card (⁅d.V, YL d c.L⁆ : Subgroup G) = 4)
    (hUQ : ⁅d.V, YL d c.L⁆ ≤ commutatorCore c.L)
    (hfix : YC d c.L ≤ centralizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G)) :
    YC d c.L ≤ centralizer (commutatorCore c.L : Set G) ∧
      YC d c.L ≤ centralizer (c.L : Set G) := by
  have hne : ⁅d.V, YL d c.L⁆ ≠ ⊥ := by
    intro h
    simp [h] at hU
  have hc := YC_centralizes_natural_core d c ha m _ hne hUQ hfix
  exact ⟨hc, YC_centralizes_of_core_fixed d c hc⟩
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions
