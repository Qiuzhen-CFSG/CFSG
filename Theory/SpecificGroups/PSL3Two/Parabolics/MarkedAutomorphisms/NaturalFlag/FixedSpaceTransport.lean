module
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.FixedSpaces
public import Theory.GroupAction.ModelConjugation
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Natural fixed spaces in the original conjugation action

A specified group isomorphism from a normalized subgroup to the binary
three-space determines its literal matrix action. Images containing the
line residual have trivial fixed subgroup. A Borel image fixes only the
coordinate point, and a line-radical image realizes that point by actual
ambient commutators. Thus the original subgroup, kernel and actors survive
transport; no independent abstract action is substituted.

Source: Aschbacher–Smith13.7.16(2), printed p.944.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
variable {G : Type*} [Group G] (H W : Subgroup G)
  (hHW : H ≤ normalizer (W : Set G)) (e : W ≃* Model)

/-- The matrix action of the actual normalizer on a marked natural subgroup. -/
noncomputable def linearAction : H →* SL :=
  slAut.symm.toMonoidHom.comp (Theory.GroupAction.ModelConjugation.action H W hHW e)

/-- Evaluation retains conjugation in the original ambient group. -/
theorem linearAction_apply (h : H) (w : W) :
    (e.symm (slAut (linearAction H W hHW e h) (e w)) : G) =
      (h : G) * (w : G) * (h : G)⁻¹ := by
  change (e.symm (slAut (slAut.symm
    (Theory.GroupAction.ModelConjugation.action H W hHW e h)) (e w)) : G) = _
  rw [MulEquiv.apply_symm_apply]
  change (e.symm (e ((W.normalizerMonoidHom (inclusion hHW h)) (e.symm (e w)))) : G) = _
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  rfl

/-- A line-parabolic residual in the literal conjugation image fixes no
nonidentity element of the marked natural subgroup. -/
theorem fixed_eq_bot_of_line_residual (J : Subgroup G)
    (hJ : lineA ≤ (J.subgroupOf H).map (linearAction H W hHW e)) :
    W ⊓ centralizer (J : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  rintro w ⟨hwW,hwC⟩
  have he : e ⟨w,hwW⟩ = 1 := line_residual_fixed_eq_one _ (by
    intro a ha
    obtain ⟨j,hj,hja⟩ := hJ ha
    apply e.symm.injective
    apply Subtype.ext
    rw [MulEquiv.symm_apply_apply, ← hja, linearAction_apply]
    change (j : G) * w * (j : G)⁻¹ = w
    rw [hwC j hj, mul_inv_cancel_right])
  have hh : (⟨w,hwW⟩ : W) = 1 := e.injective (he.trans e.map_one.symm)
  exact congrArg Subtype.val hh

/-- In an actual marked natural action, every Sylow fixed element is a
commutator with the subgroup inducing the line radical. -/
theorem fixed_le_commutator_of_line_radical (T U : Subgroup G)
    (hT : borelSL ≤ (T.subgroupOf H).map (linearAction H W hHW e))
    (hU : lineV ≤ (U.subgroupOf H).map (linearAction H W hHW e)) :
    W ⊓ centralizer (T : Set G) ≤ ⁅W,U⁆ := by
  rintro w ⟨hwW,hwC⟩
  have hp : e ⟨w,hwW⟩ ∈ point := borel_fixed_mem_point _ (by
    intro a ha
    obtain ⟨t,ht,hta⟩ := hT ha
    apply e.symm.injective
    apply Subtype.ext
    rw [MulEquiv.symm_apply_apply, ← hta, linearAction_apply]
    change (t : G) * w * (t : G)⁻¹ = w
    rw [hwC t ht, mul_inv_cancel_right])
  obtain ⟨v,a,ha,hv⟩ := point_displacement _ hp
  obtain ⟨u,hu,hua⟩ := hU ha
  have hcomm : w = ⁅(e.symm v : G), (u : G)⁆ := by
    have hh := congrArg (fun x : Model => (e.symm x : G)) hv
    simp only [MulEquiv.symm_apply_apply, map_mul, map_inv, coe_mul, coe_inv] at hh
    rw [← hua] at hh
    have happ := linearAction_apply H W hHW e u (e.symm v)
    rw [MulEquiv.apply_symm_apply] at happ
    rw [happ] at hh
    rw [hh]
    simp only [commutatorElement_def]
    group
  rw [hcomm]
  exact commutator_mem_commutator (e.symm v).property hu

end Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
