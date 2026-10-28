module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Projection

/-!
# From the projected centre to the exact 15.3.11(12) premise

The equality C_L(Z_L) = C_L(Z), together with Z ≤ V and monotonicity of
the two-residual, transfers noncentrality from Z_L and O²(Y₊∩P) to
V and O²(Y∩P). The central supplement is retained through the splitting.
Only after this transfer do we apply the explicit earlier source implication.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(12) and 15.3.24, printed pp.1123–1124 and 1129.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic
variable {G : Type*} [Group G] {d : LocalData G} {L : Subgroup G}

/-- The nontrivial projected action implies precisely the action premise of 15.3.11(12). -/
theorem projected_action_transfer [Finite G] [IsElementaryAbelian 2 (d.componentSpan L)]
    (hsplit : spanCommutator d L ⊔ d.Z =
      spanCommutator d L ⊔ centralSupplement d L)
    {P : Subgroup G} (hPL : P ≤ L)
    (hact : ⁅projectedCenter d L, Stellmacher.twoResidualAmbient (d.Yplus ⊓ P)⁆ ≠ ⊥) :
    ⁅d.V, Stellmacher.twoResidualAmbient (d.Y ⊓ P)⁆ ≠ ⊥ := by
  have hYY : d.Yplus ≤ d.Y := by
    rcases d.choice with he | ⟨_, he⟩
    · exact he.le
    · rw [he]
      exact (map_subtype_le _).trans inf_le_left
  have hm : Stellmacher.twoResidualAmbient (d.Yplus ⊓ P) ≤
      Stellmacher.twoResidualAmbient (d.Y ⊓ P) := by
    simp only [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    exact embedded_pResidual_mono 2 (inf_le_inf_right P hYY)
  have hresL : Stellmacher.twoResidualAmbient (d.Yplus ⊓ P) ≤ L :=
    (map_subtype_le _).trans (inf_le_right.trans hPL)
  intro hzero
  have hC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hCZ : Stellmacher.twoResidualAmbient (d.Yplus ⊓ P) ≤ centralizer (d.Z : Set G) :=
    (hm.trans hC).trans (centralizer_le (le_conjugateSpanBy _ _))
  have hp : Stellmacher.twoResidualAmbient (d.Yplus ⊓ P) ≤
      L ⊓ centralizer (projectedCenter d L : Set G) := by
    rw [projectedCenter_centralizer d L hsplit]
    exact le_inf hresL hCZ
  exact hact (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mpr (hp.trans inf_le_right)))

/-- Apply the earlier source implication only after establishing its exact V-residual premise. -/
theorem characteristic_exclusion_of_projected_action [Finite G]
    [IsElementaryAbelian 2 (d.componentSpan L)] {I P : Subgroup G}
    (hsplit : spanCommutator d L ⊔ d.Z =
      spanCommutator d L ⊔ centralSupplement d L)
    (hPL : P ≤ L) (hPI : P ≤ I) (hPM : ¬ P ≤ d.M)
    (hact : ⁅projectedCenter d L, Stellmacher.twoResidualAmbient (d.Yplus ⊓ P)⁆ ≠ ⊥)
    (h11 : ∀ J : Subgroup G, J ≤ I →
      ⁅d.V, Stellmacher.twoResidualAmbient (d.Y ⊓ J)⁆ ≠ ⊥ → ¬ J ≤ d.M →
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ ((C.map d.S.subtype).subgroupOf (J ⊔ d.S)).Normal) :
    ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf (P ⊔ d.S)).Normal :=
  h11 P hPI (projected_action_transfer hsplit hPL hact) hPM


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic

end
