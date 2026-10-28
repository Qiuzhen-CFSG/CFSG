module
public import Theory.Representation.BinaryNaturalDual.Action
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.Split

/-!
# Involution displacement in natural-plus-dual coordinates

Contragredience preserves individual displacement rank, so inner actors
move an even-dimensional subspace of the natural-plus-dual module. An
outer involution exchanges the summands and moves one full summand.
The inner/graph description of Aut(GLₙ(2)), for n = 4 or 5, therefore
excludes every nontrivial rank-one involution in the coordinate action.

This is the natural-plus-dual step in the marked partner-chief rank-two
argument for Aschbacher--Smith, original 15.2.27(2), printed p.1119
(refs/quasithin.pdf p.1136).
-/

public noncomputable section
open Representation Representation.BinaryOffender
namespace BinaryNaturalDual
open BinaryLinear.OuterCyclic Representation.RankTwo.Imprimitive

/-- Natural and contragredient displacement ranks are equal. -/
theorem naturalDual_displacement_even {n : ℕ} (g : LinearGroup n) :
    Module.finrank (ZMod 2) (LinearMap.range (naturalDualRepresentation g - 1)) =
      2 * Module.finrank (ZMod 2) (LinearMap.range (g.toLinearMap - 1)) := by
  let ρ : Representation (ZMod 2) (LinearGroup n) (BinaryLinear.OuterCyclic.Space n) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have he : naturalDualRepresentation = ρ.prod ρ.dual := by
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro v
    exact naturalDualRepresentation_apply a v
  have hr := fixedCodim_prod ρ ρ.dual (Subgroup.zpowers g)
  rw [fixedCodim_zpowers_dual, fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank] at hr
  rw [he]
  exact hr.trans (by simp only [two_mul]; rfl)

/-- An outer involution moves one full summand of the coordinate module. -/
theorem CoordinateAction.graph_inner_involution_displacement {n : ℕ}
    (d : CoordinateAction n) (g : LinearGroup n)
    (ha : (graphLinear n * MulAut.conj g) ^ 2 = 1) :
    Module.finrank (ZMod 2)
      (LinearMap.range (d.representation (graphLinear n * MulAut.conj g) - 1)) = n := by
  let f := dotProductEquiv (ZMod 2) (Fin n)
  have hh := finrank_of_exchanges (d.representation (graphLinear n * MulAut.conj g))
    (f.toLinearMap.comp g.toLinearMap)
    (f.symm.toLinearMap.comp g.symm.dualMap)
    (fun v w => by
      rw [map_mul, Module.End.mul_apply, d.on_inner, d.on_graph,
        naturalDualRepresentation_apply, coordinateSwap_apply]
      rfl)
    (by rw [← map_mul, ← pow_two, ha, map_one])
  simpa [BinaryLinear.OuterCyclic.Space] using hh

/-- In degrees four and five, a nonidentity involution operator has rank at least two. -/
theorem CoordinateAction.involution_displacement_ge_two {n : ℕ}
    (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    (a : MulAut (LinearGroup n)) (ha : a ^ 2 = 1) (hne : d.representation a ≠ 1) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (d.representation a - 1)) := by
  obtain ⟨g,rfl | rfl⟩ := inner_graph hn a
  · have he : d.representation (MulAut.conj g) = naturalDualRepresentation g := by
      apply LinearMap.ext
      intro v
      exact d.on_inner g v
    have hr := naturalDual_displacement_even g
    rw [← he] at hr
    have hp : 0 < Module.finrank (ZMod 2)
        (LinearMap.range (d.representation (MulAut.conj g) - 1)) := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hne (sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
    rw [hr]
    have hp' : 0 < Module.finrank (ZMod 2) (LinearMap.range (g.toLinearMap - 1)) := by
      rw [hr] at hp
      omega
    omega
  · rw [d.graph_inner_involution_displacement g ha]
    omega

end BinaryNaturalDual
