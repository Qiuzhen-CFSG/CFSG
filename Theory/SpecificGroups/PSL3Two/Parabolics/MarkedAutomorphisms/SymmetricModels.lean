module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Symmetric and alternating models of the marked parabolics

The line parabolic acts faithfully on the four vectors whose last coordinate
is one. Its order is 24, so this action identifies it with S₄. Transporting
the intrinsic two-residual gives A₄. The point identifications use the same
fixed diagram involution as the residual and two-core identifications;
no independent choice of an ambient group identification is made.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.21(1), printed p.957, covered-A₆ paragraph.
-/

public section
open Matrix Subgroup
namespace Matrix.PSL3Two.MarkedAutomorphisms
private abbrev Four := ZMod 2 × ZMod 2
private def affineVec (x : Four) : Fin 3 → ZMod 2 := ![x.1,x.2,1]
private def firstTwo (v : Fin 3 → ZMod 2) : Four := (v 0, v 1)
private def affineAct (g : SL) (x : Four) : Four :=
  firstTwo (g.val.mulVec (affineVec x))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem line_last_entry : ∀ g : SL, g ∈ lineParabolicSL → g.val 2 2 = 1 := by
  decide +kernel

private theorem affineVec_act (g : SL) (hg : g ∈ lineParabolicSL) (x : Four) :
    affineVec (affineAct g x) = g.val.mulVec (affineVec x) := by
  have h := (mem_lineParabolicSL_iff g).mp hg
  funext i
  fin_cases i
  · rfl
  · rfl
  · simp [affineVec, mulVec, dotProduct, Fin.sum_univ_three, h.1, h.2, line_last_entry g hg]

private theorem affineAct_mul (g h : SL) (hh : h ∈ lineParabolicSL) (x : Four) :
    affineAct (g * h) x = affineAct g (affineAct h x) := by
  have he : (g * h).val.mulVec (affineVec x) =
      g.val.mulVec (affineVec (affineAct h x)) := by
    rw [affineVec_act h hh, mulVec_mulVec]
    rfl
  exact congrArg firstTwo he

private theorem affineAct_one (x : Four) : affineAct 1 x = x := by
  simp [affineAct, firstTwo, affineVec]

private def linePerm (g : lineParabolicSL) : Equiv.Perm Four where
  toFun := affineAct g
  invFun := affineAct (g : SL)⁻¹
  left_inv x := by
    rw [← affineAct_mul _ _ g.property, inv_mul_cancel, affineAct_one]
  right_inv x := by
    rw [← affineAct_mul _ _ (lineParabolicSL.inv_mem g.property),
      mul_inv_cancel, affineAct_one]

private def linePermHom : lineParabolicSL →* Equiv.Perm Four where
  toFun := linePerm
  map_one' := by
    apply Equiv.ext
    intro x
    exact affineAct_one x
  map_mul' g h := by
    apply Equiv.ext
    intro x
    exact affineAct_mul g h h.property x

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem affine_faithful : ∀ g : SL, g ∈ lineParabolicSL →
    affineAct g (0,0) = (0,0) → affineAct g (1,0) = (1,0) →
    affineAct g (0,1) = (0,1) → g = 1 := by decide +kernel

private theorem linePermHom_injective : Function.Injective linePermHom := by
  apply (MonoidHom.ker_eq_bot_iff linePermHom).mp
  apply le_bot_iff.mp
  intro g hg
  apply Subtype.ext
  apply affine_faithful g g.property
  · exact Equiv.congr_fun hg (0,0)
  · exact Equiv.congr_fun hg (1,0)
  · exact Equiv.congr_fun hg (0,1)

private noncomputable def lineEquivPerm : lineParabolicSL ≃* Equiv.Perm Four :=
  MulEquiv.ofBijective linePermHom
    ((Nat.bijective_iff_injective_and_card linePermHom).mpr ⟨linePermHom_injective, by
      rw [card_lineParabolicSL, Nat.card_eq_fintype_card, Fintype.card_perm]
      norm_num [Four, Nat.factorial]⟩)
/-- The line parabolic acts faithfully as all permutations of its four affine points. -/
noncomputable def lineEquivSymmetric : lineParabolicSL ≃* Equiv.Perm (Fin 4) :=
  lineEquivPerm.trans (Equiv.permCongrHom
    (Finite.equivFinOfCardEq (by rw [Nat.card_eq_fintype_card]; decide : Nat.card Four = 4)))

/-- The point identification is transported from the line by the fixed diagram map. -/
noncomputable def pointEquivSymmetric : pointParabolicSL ≃* Equiv.Perm (Fin 4) :=
  ((diagram.subgroupMap pointParabolicSL).trans
    (MulEquiv.subgroupCongr pointParabolic_map_diagram)).trans lineEquivSymmetric

/-- An actual symmetric-four identification identifies the embedded intrinsic residual with A₄. -/
noncomputable def residualEquivAlternating (P : Subgroup SL)
    (e : P ≃* Equiv.Perm (Fin 4)) : residual P ≃* alternatingGroup (Fin 4) :=
  ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).symm.trans
    (((pResidual 2 P).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr ((map_pResidual 2 e).trans
        (Equiv.Perm.twoResidual_eq_alternating (Fin 4)))))

/-- The point residual is the actual alternating group on four letters. -/
noncomputable def pointResidualEquivAlternating :
    residual pointParabolicSL ≃* alternatingGroup (Fin 4) :=
  residualEquivAlternating pointParabolicSL pointEquivSymmetric

/-- The line residual is the actual alternating group on four letters. -/
noncomputable def lineResidualEquivAlternating :
    residual lineParabolicSL ≃* alternatingGroup (Fin 4) :=
  residualEquivAlternating lineParabolicSL lineEquivSymmetric

end Matrix.PSL3Two.MarkedAutomorphisms
