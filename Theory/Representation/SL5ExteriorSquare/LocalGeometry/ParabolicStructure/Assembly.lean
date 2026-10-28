module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Assembly.Quotients
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Assembly.OrthogonalAction
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors

/-!
# Intrinsic structure of all four exterior parabolics

The Levi and residual calculations identify the actual source quotient actors.
We transport the natural and orthogonal representations through the proved
linear equivalences and check, on every quotient representative, that the
result is the original exterior action. These identities establish descent;
the equivalences therefore concern the actual modules, not merely models of
the same dimension. On V₃ the actor is explicitly twisted by inverse transpose.

The four group clauses are assembled below, and the actual chief-series theorem
`exteriorStabilizer_V₁_chief_chain` is re-exported without factor hypotheses.
For V₆, the representation equivalence uses the Pfaffian isometry to the split
form and the actual Ω⁺₆ subgroup. The quotient V/V₆ is also equivariantly
isomorphic to R₆ = O₂(L₆T) under conjugation. All residual quotients use
Lᵢ ∩ Rᵢ; only at the perfect endpoints is Rᵢ contained in Lᵢ.

Source: Aschbacher–Smith, Lemma 12.5.2, printed p.817/PDF p.834.
Natural flag dimensions k = 2,3,1,4 correspond to source indices i = 1,3,4,6.
-/

@[expose] public noncomputable section
open scoped MatrixGroups
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- The natural V₃ actor includes the contragredient twist. -/
def V₃ResidualQuotientAction : Representation (ZMod 2)
    (parabolicResidual 3 ⧸ (parabolicResidualTwoCore 3).subgroupOf (parabolicResidual 3)) V₃ :=
  V₃Equiv.symm.conjRingEquiv.toMonoidHom.comp
    ((specialLinearNatural 3).comp parabolicThreeResidualNaturalEquiv.toMonoidHom)

/-- The quotient action on representatives is the original exterior action. -/
@[simp] theorem V₃ResidualQuotientAction_mk (g : parabolicResidual 3) (v : V₃) :
    V₃ResidualQuotientAction (QuotientGroup.mk' _ g) v =
      V₃Action (Subgroup.inclusion (parabolicResidual_le 3) g) v := by
  apply V₃Equiv.injective
  change V₃Equiv (V₃Equiv.symm
    (specialLinearNatural 3 (parabolicThreeResidualNaturalEquiv (QuotientGroup.mk' _ g))
      (V₃Equiv v))) = _
  rw [LinearEquiv.apply_symm_apply, parabolicThreeResidualNaturalEquiv_mk]
  exact (V₃Equiv_intertwines _ _).symm

/-- A genuine natural-module equivalence for L₃/(L₃ ∩ R₃). -/
def V₃ResidualQuotientEquivNatural : V₃ResidualQuotientAction.Equiv
    ((specialLinearNatural 3).comp parabolicThreeResidualNaturalEquiv.toMonoidHom) :=
  .mk V₃Equiv (fun g => by
    apply LinearMap.ext
    intro v
    exact V₃Equiv.apply_symm_apply _)

/-- The descended action on V₄; the next theorem identifies its actual representatives. -/
def V₄ResidualQuotientAction : Representation (ZMod 2)
    (parabolicResidual 1 ⧸ (parabolicResidualTwoCore 1).subgroupOf (parabolicResidual 1)) V₄ :=
  V₄Equiv.symm.conjRingEquiv.toMonoidHom.comp
    ((specialLinearNatural 4).comp parabolicOneResidualQuotientEquiv.toMonoidHom)

/-- The quotient action on representatives is the original exterior action. -/
@[simp] theorem V₄ResidualQuotientAction_mk (g : parabolicResidual 1) (v : V₄) :
    (V₄ResidualQuotientAction (QuotientGroup.mk' _ g) v).val = exteriorAction 2 g.val v.val := by
  have h := V₄Equiv_natural (Subgroup.inclusion (parabolicResidual_le 1) g) v
  have he : V₄ResidualQuotientAction (QuotientGroup.mk' _ g) v =
      ⟨exteriorAction 2 g.val v.val,
        (parabolic_one_le_stabilizer_V₄ ((parabolicResidual_le 1) g.property) v.val).mpr
          v.property⟩ := by
    apply V₄Equiv.injective
    change V₄Equiv (V₄Equiv.symm
      (specialLinearNatural 4 (parabolicOneResidualQuotientEquiv (QuotientGroup.mk' _ g))
        (V₄Equiv v))) = _
    rw [LinearEquiv.apply_symm_apply, parabolicOneResidualQuotientEquiv_mk]
    exact h.symm
  exact congrArg Subtype.val he

/-- The source V₄ is the natural module for the actual residual quotient L₄/R₄. -/
def V₄ResidualQuotientEquivNatural : V₄ResidualQuotientAction.Equiv
    ((specialLinearNatural 4).comp parabolicOneResidualQuotientEquiv.toMonoidHom) :=
  .mk V₄Equiv (fun g => by
    apply LinearMap.ext
    intro v
    exact V₄Equiv.apply_symm_apply _)

/-- The descended action of L₆/R₆ on the literal vector-space quotient V/V₆. -/
def quotientSixResidualQuotientAction : Representation (ZMod 2)
    (parabolicResidual 4 ⧸ (parabolicResidualTwoCore 4).subgroupOf (parabolicResidual 4))
      (V ⧸ V₆) :=
  shearQuotientEquiv.symm.conjRingEquiv.toMonoidHom.comp
    ((specialLinearNatural 4).comp parabolicFourResidualQuotientEquiv.toMonoidHom)

/-- The quotient action on representatives is the original exterior action. -/
@[simp] theorem quotientSixResidualQuotientAction_mk (g : parabolicResidual 4) (v : V ⧸ V₆) :
    quotientSixResidualQuotientAction (QuotientGroup.mk' _ g) v =
      quotientSixAction (Subgroup.inclusion (parabolicResidual_le 4) g) v := by
  apply shearQuotientEquiv.injective
  change shearQuotientEquiv (shearQuotientEquiv.symm
    (specialLinearNatural 4 (parabolicFourResidualQuotientEquiv (QuotientGroup.mk' _ g))
      (shearQuotientEquiv v))) = _
  rw [LinearEquiv.apply_symm_apply, parabolicFourResidualQuotientEquiv_mk]
  exact (shearQuotientEquiv_natural _ _).symm

/-- The actual quotient V/V₆ is natural for L₆/R₆ through its upper SL₄ block. -/
def quotientSixResidualQuotientEquivNatural : quotientSixResidualQuotientAction.Equiv
    ((specialLinearNatural 4).comp parabolicFourResidualQuotientEquiv.toMonoidHom) :=
  .mk shearQuotientEquiv (fun g => by
    apply LinearMap.ext
    intro v
    exact shearQuotientEquiv.apply_symm_apply _)

/-- The action of the actual Ω⁺₆ subgroup on its defining split quadratic space. -/
def omegaSixNatural : Representation (ZMod 2) (ClassicalOrthogonal.OmegaPlus 3 (ZMod 2))
    (ClassicalOrthogonal.VectorD 3 (ZMod 2)) where
  toFun g := g.val.val.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The genuine source actor L₆/R₆ is the actual Ω⁺₆(2) subgroup. -/
def parabolicFourResidualOmegaEquiv :
    (parabolicResidual 4 ⧸ (parabolicResidualTwoCore 4).subgroupOf (parabolicResidual 4)) ≃*
      ClassicalOrthogonal.OmegaPlus 3 (ZMod 2) := parabolicFourResidualQuotientEquiv.trans sl4TwoOmegaEquiv

/-- The descended action of the source residual quotient on the actual V₆. -/
def V₆ResidualQuotientAction : Representation (ZMod 2)
    (parabolicResidual 4 ⧸ (parabolicResidualTwoCore 4).subgroupOf (parabolicResidual 4)) V₆ :=
  v6QuadraticIsometry.toLinearEquiv.symm.conjRingEquiv.toMonoidHom.comp
    (omegaSixNatural.comp parabolicFourResidualOmegaEquiv.toMonoidHom)

/-- The quotient action on representatives is the original exterior action. -/
@[simp] theorem V₆ResidualQuotientAction_mk (g : parabolicResidual 4) (v : V₆) :
    V₆ResidualQuotientAction (QuotientGroup.mk' _ g) v =
      v6Action (Subgroup.inclusion (parabolicResidual_le 4) g) v := by
  apply v6QuadraticIsometry.toLinearEquiv.injective
  change v6QuadraticIsometry.toLinearEquiv (v6QuadraticIsometry.toLinearEquiv.symm
    ((sl4TwoOmegaEquiv (parabolicFourResidualQuotientEquiv (QuotientGroup.mk' _ g))).val.val
      (v6QuadraticIsometry v))) = _
  rw [LinearEquiv.apply_symm_apply, parabolicFourResidualQuotientEquiv_mk]
  exact (v6QuadraticIsometry_action _ _).symm

/-- The Pfaffian isometry is a genuine equivalence with the defining Ω⁺₆ module. -/
def V₆ResidualQuotientEquivOrthogonal : V₆ResidualQuotientAction.Equiv
    (omegaSixNatural.comp parabolicFourResidualOmegaEquiv.toMonoidHom) :=
  .mk v6QuadraticIsometry.toLinearEquiv (fun g => by
    apply LinearMap.ext
    intro v
    exact v6QuadraticIsometry.toLinearEquiv.apply_symm_apply _)

/-- The source natural quotient and R₆ are equivariantly isomorphic, with actual conjugation. -/
theorem quotientSixRadicalEquiv_residual_action (g : parabolicResidual 4) (v : V ⧸ V₆) :
    (quotientSixRadicalEquiv
      (Multiplicative.ofAdd (quotientSixResidualQuotientAction (QuotientGroup.mk' _ g) v)) : Group) =
      g.val * (quotientSixRadicalEquiv (Multiplicative.ofAdd v) : Group) * g.val⁻¹ := by
  rw [quotientSixResidualQuotientAction_mk]
  exact quotientSixRadicalEquiv_action _ _

/-- The descended source quotient acts by isometries of the actual Pfaffian form. -/
theorem V₆ResidualQuotientAction_preserves_form
    (g : parabolicResidual 4 ⧸ (parabolicResidualTwoCore 4).subgroupOf (parabolicResidual 4))
    (v : V₆) : v6QuadraticForm (V₆ResidualQuotientAction g v) = v6QuadraticForm v := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ g
  rw [V₆ResidualQuotientAction_mk]
  exact v6QuadraticForm_invariant _ _

/-- The four literal exterior stabilizers, Levi quotients, residual quotients,
and perfect endpoint equalities in the source. Products use coordinate-block order. -/
theorem exterior_parabolic_groups :
    (exteriorStabilizer V₁ = parabolic 2 ∧
      Nonempty ((parabolic 2 ⧸ pCore 2 (parabolic 2)) ≃*
        SL(2, ZMod 2) × SL(3, ZMod 2)) ∧
      Nonempty ((parabolicResidual 2 ⧸
        (parabolicResidualTwoCore 2).subgroupOf (parabolicResidual 2)) ≃* SL(3, ZMod 2))) ∧
    (exteriorStabilizer V₃ = parabolic 3 ∧
      Nonempty ((parabolic 3 ⧸ pCore 2 (parabolic 3)) ≃*
        SL(3, ZMod 2) × SL(2, ZMod 2)) ∧
      Nonempty ((parabolicResidual 3 ⧸
        (parabolicResidualTwoCore 3).subgroupOf (parabolicResidual 3)) ≃* SL(3, ZMod 2))) ∧
    (exteriorStabilizer V₄ = parabolic 1 ∧ parabolicResidual 1 = parabolic 1 ∧
      Nonempty ((parabolic 1 ⧸ pCore 2 (parabolic 1)) ≃* SL(4, ZMod 2)) ∧
      Nonempty ((parabolicResidual 1 ⧸
        (parabolicResidualTwoCore 1).subgroupOf (parabolicResidual 1)) ≃* SL(4, ZMod 2))) ∧
    (exteriorStabilizer V₆ = parabolic 4 ∧ parabolicResidual 4 = parabolic 4 ∧
      Nonempty ((parabolic 4 ⧸ pCore 2 (parabolic 4)) ≃* SL(4, ZMod 2)) ∧
      Nonempty ((parabolicResidual 4 ⧸
        (parabolicResidualTwoCore 4).subgroupOf (parabolicResidual 4)) ≃* SL(4, ZMod 2))) := by
  exact ⟨⟨exteriorStabilizer_V₁_eq_parabolic, ⟨parabolicTwoQuotientEquiv⟩,
      ⟨parabolicTwoResidualQuotientEquiv⟩⟩,
    ⟨exteriorStabilizer_V₃_eq_parabolic, ⟨parabolicThreeQuotientEquiv⟩,
      ⟨parabolicThreeResidualQuotientEquiv⟩⟩,
    ⟨exteriorStabilizer_V₄_eq_parabolic, parabolicResidual_one,
      ⟨parabolicOneQuotientEquiv⟩, ⟨parabolicOneResidualQuotientEquiv⟩⟩,
    ⟨exteriorStabilizer_V₆_eq_parabolic, parabolicResidual_four,
      ⟨parabolicFourQuotientEquiv⟩, ⟨parabolicFourResidualQuotientEquiv⟩⟩⟩

end Representation.SL5ExteriorSquare
