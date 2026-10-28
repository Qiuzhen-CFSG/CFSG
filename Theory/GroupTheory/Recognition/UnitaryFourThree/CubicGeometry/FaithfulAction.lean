module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.ComponentAction
/-!
# Faithful action on the original cubic graph

The action kernel N fixes both W and a chosen opposite cubic, hence lies
in their common stabilizer K. Normality gives [N,D]≤N∩D=1. The literal
centralizer C_G(D)=W then places N inside D as well, so N=1. This embeds
the original ambient group into the automorphism group of its graph.
Source: Aschbacher, Sporadic Groups (1994),45.10–45.11, pp.248–249.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

@[expose] noncomputable def pointAction : G →* Equiv.Perm c.points := by
  let := c.conjugationAction
  exact MulAction.toPermHom G c.points

omit [Finite G] in
theorem pointAction_apply (g : G) (U : c.points) : c.pointAction g U=c.conjugatePoint U g := rfl

theorem pointAction_injective : Function.Injective c.pointAction := by
  let N := c.pointAction.ker
  have hN (U : c.points) : N≤normalizer (U.val:Set G) := by
    intro g hg
    have hh := DFunLike.congr_fun hg U
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact congrArg Subtype.val hh
  obtain ⟨Y,hYL,hY,hne,-,hK⟩ := c.exists_complement_fixed_opposite_cubic
  have hNK : N≤c.K := by
    rw [←c.opposite_cubic_common_normalizer hYL hY hne hK]
    exact le_inf (hN ⟨c.W,c.point_mem⟩) (hN ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩)
  have hND : Disjoint N c.D := c.complement_disjoint.symm.mono_left hNK
  have hcD : ⁅N,c.D⁆≤c.D := le_normalizer_iff_commutator_le_right.mp
    ((hN ⟨c.W,c.point_mem⟩).trans (CubicLine.normalizer_normalizes_oddKernel c.W))
  have hcN : ⁅N,c.D⁆≤N := commutator_le_left N c.D
  have hc : ⁅N,c.D⁆=⊥ := bot_unique ((le_inf hcN hcD).trans hND.le_bot)
  have hNW : N≤c.W := c.odd_centralizer ▸ commutator_eq_bot_iff_le_centralizer.mp hc
  have hWD : c.W≤c.D := c.odd_fixed.ge.trans inf_le_left
  have hNb : N=⊥ := bot_unique ((le_inf le_rfl (hNW.trans hWD)).trans hND.le_bot)
  exact (MonoidHom.ker_eq_bot_iff c.pointAction).mp hNb

@[expose] noncomputable def graphAction : G →* (c.collinearity ≃g c.collinearity) where
  toFun := c.conjugationGraphIso
  map_one' := by
    apply RelIso.ext
    intro U
    exact Subtype.ext (conjBy_one U.val)
  map_mul' g g' := by
    apply RelIso.ext
    intro U
    exact Subtype.ext (conjBy_conjBy U.val g' g).symm

theorem graphAction_injective : Function.Injective c.graphAction := by
  intro g g' hh
  apply c.pointAction_injective
  apply Equiv.ext
  intro U
  exact DFunLike.congr_fun hh U
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
