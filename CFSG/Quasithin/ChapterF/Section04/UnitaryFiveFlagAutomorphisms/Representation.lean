module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.EndpointRigidity
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.ScalarRepresentative
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.LeviRigidity

/-!
# Native involutory U₅(4) flag representation

Normalize the literal residual quotient and an order-fifteen torus. The
full radical scalar is represented by one unitary diagonal; twisted-tensor
cohomology kills the remaining central Levi cocycle. Agreement on the
whole plane residual detects the global flag automorphism through the
opposite perfect endpoint. Restoring the actual native inner correction
and standard graph gives the required unitary graph formula, including
nonidentity coefficients and the unchanged fifth-root scalar kernel.

Source: Aschbacher–Smith F.4.29(2), printed p.289 of refs/quasithin.pdf,
whose automorphism assertion cites AS76a.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
open Subgroup GreenBook.UnitaryFive Theory.SpecificGroups.UnitaryFive
variable (U : Model 4)

/-- The exact flag-preserving unitary diagonal for the remaining radical scalar. -/
def scalarFlag (k : U.Fˣ) : flagAutomorphisms U :=
  ⟨Descent.unitaryConj U.form
      (FlagAutomorphisms.scalarUnitary U.form U.rightLeviTrace U.rightLeviTrace_spec U.matrix k),
    FlagAutomorphisms.scalarUnitary_flag U.form U.rightLeviTrace U.rightLeviTrace_spec U.matrix k⟩

theorem scalarFlag_coordinates (k : U.Fˣ) (p : PlaneCore.PlaneSemidirect U.form) :
    (scalarFlag U k).val (rightCoordinates U p).val =
      (rightCoordinates U ⟨FlagAutomorphisms.scalarParameter U.form (k:U.F) p.left,p.right⟩).val := by
  rw [rightCoordinates_val,rightCoordinates_val]
  conv_lhs => rw [←SemidirectProduct.inl_left_mul_inr_right p,map_mul]
  conv_rhs => rw [←SemidirectProduct.inl_left_mul_inr_right
    (⟨FlagAutomorphisms.scalarParameter U.form (k:U.F) p.left,p.right⟩ : PlaneCore.PlaneSemidirect U.form),map_mul]
  change Descent.unitaryConj U.form _ (_*_) = _
  simp only [map_mul,FlagAutomorphisms.nativePlane_inl,FlagAutomorphisms.nativePlane_inr,
    FlagAutomorphisms.scalarUnitary_radical,FlagAutomorphisms.scalarUnitary_levi]

/-- Quotient and torus normalization determines one whole native unitary actor. -/
theorem normalized_eq_scalarFlag (a : flagAutomorphisms U) (ha : rightLinearAction U a = 1)
    (k : U.F) (hk : k ≠ 0) (t : U.Fˣ) (ht : orderOf t = 15)
    (hfix : rightCoordinateAction U a (SemidirectProduct.inr (PlaneCore.ResidualAction.diagonalActor t)) =
      SemidirectProduct.inr (PlaneCore.ResidualAction.diagonalActor t))
    (hx : ∀ u, (rightRadicalAction U a u).x = k • u.x)
    (hz : ∀ u, (rightRadicalAction U a u).z = (k * U.form.conj k) • u.z) :
    a = scalarFlag U (Units.mk0 k hk) := by
  have hright := rightCoordinateAction_right U a ha
  have hcentral := FlagAutomorphisms.leviDeviation_center U.form U.rightLeviTrace U.rightLeviTrace_spec
    (rightCoordinateAction U a) hright k hx hz
  have hdev := FlagAutomorphisms.leviDeviation_eq_one_of_center U.form U.conjugation
    U.rightLeviTrace U.rightLeviTrace_spec (rightCoordinateAction U a) hright hcentral t ht hfix
  have he (p : PlaneCore.PlaneSemidirect U.form) : rightCoordinateAction U a p =
      ⟨FlagAutomorphisms.scalarParameter U.form k p.left,p.right⟩ := by
    rw [FlagAutomorphisms.residualActor_formula U.form _ hright,hdev,mul_one]
    apply SemidirectProduct.ext
    · exact PlaneCore.Parameters.ext (hx p.left) (hz p.left)
    · rfl
  apply rightLocalAction_injective U
  apply MulEquiv.ext
  intro x
  obtain ⟨p,rfl⟩ := (rightCoordinates U).surjective x
  apply Subtype.ext
  simp only [rightLocalAction_val]
  rw [scalarFlag_coordinates]
  have hh := congrArg Subtype.val (rightCoordinateAction_apply U a p)
  rw [he,rightLocalAction_val] at hh
  exact hh.symm

/-- The native q=4 flag involution has one actual five-dimensional unitary twist. -/
theorem involution_eq_unitary_graph (a : flagAutomorphisms U) (ha : a^2 = 1)
    (hc : rightCoefficient U a = U.form.conj) :
    ∃ u : U.form.unitarySubgroup,
      a.val = Descent.unitaryConj U.form u * GraphFixed.projectiveAut U.form U.matrix := by
  obtain ⟨b,γ,k,t,_,hk,ht,he,hq,hfix,hx,hz,_,_⟩ := involution_plane_normalize U a ha hc
  have hγ := normalized_eq_scalarFlag U γ hq k hk t ht hfix hx hz
  obtain ⟨g,hg⟩ := project_surjective U.form b.val
  let s := FlagAutomorphisms.scalarUnitary U.form U.rightLeviTrace U.rightLeviTrace_spec U.matrix (Units.mk0 k hk)
  refine ⟨⟨g.val,g.property.1⟩ * s,?_⟩
  rw [he,hγ,Descent.unitaryConj_mul,Descent.unitaryConj_special,hg]
  rfl

/-- Nonidentity of the actual residual coefficient suffices; the involution determines conjugation. -/
theorem involution_eq_unitary_graph_of_coefficient_ne_one (a : flagAutomorphisms U)
    (ha : a^2 = 1) (hc : rightCoefficient U a ≠ 1) :
    ∃ u : U.form.unitarySubgroup,
      a.val = Descent.unitaryConj U.form u * GraphFixed.projectiveAut U.form U.matrix :=
  involution_eq_unitary_graph U a ha (rightCoefficient_eq_conj U a ha hc)
end CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
