module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.OuterImageComparison.CentralQuotient
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.OuterImageComparison.MatrixComparison

/-!
# Realizing the certified right-conjugation tables in quotient coordinates

A coordinate isomorphism for the actual N/<t> is required to send each of
the twelve noncentral generators to the corresponding standard basis vector.
The published thirteen-element conjugation tables then identify the action
matrices: dropping the central bit is checked on every generator. Generation
extends these identities to the entire quotient.

Right conjugation by g is the inverse of the left-conjugation action used
by `MulAut`; `rowAction` likewise uses inverse right multiplication. These
two inverses give the displayed generator images without transposing or
reversing the source words. The certified change of basis embeds the literal
`LowerBound.quotientSubgroup` in this action image, giving the desired
cardinality inequality conditional only on the actual coordinate isomorphism.

Source motivation: GLS3 Table 5.3i, printed p.270; concrete words and matrices
are in `Certificates.Relations` and `Presentation/source/README.md`.
-/

set_option maxRecDepth 4000
@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
namespace OuterImageComparison
open NormalClosureControl LowerBound Matrix

abbrev Coordinates := CentralQuotient ≃* Multiplicative BinaryVector

def vectorBasis : Fin 13 → Multiplicative BinaryVector :=
  Fin.cases 1 (fun i => Multiplicative.ofAdd (Pi.single i 1))

/-- The central generator is zero, and generator i+1 is standard coordinate i. -/
def RespectsBasis (e : Coordinates) : Prop := ∀ i, e (quotientBasis i) = vectorBasis i

def coordinateAction (e : Coordinates) : localSubgroup →* MulAut (Multiplicative BinaryVector) :=
  (MulAut.congr e).toMonoidHom.comp quotientAction

theorem quotientAction_basis_inv (g : localSubgroup) (masks : Fin 13 → ℕ)
    (h : ∀ i, g⁻¹ * basis i * g = maskProduct basis (masks i)) (i : Fin 13) :
    quotientAction g⁻¹ (quotientBasis i) =
      projection (maskProduct basisElement (masks i)) := by
  apply congrArg projection
  apply Subtype.ext
  change g⁻¹ * basis i * (g⁻¹)⁻¹ =
    localNormalClosure.subtype (maskProduct basisElement (masks i))
  rw [inv_inv, map_maskProduct]
  exact h i

theorem coordinates_maskProduct (e : Coordinates) (he : RespectsBasis e) (m : ℕ) :
    e (projection (maskProduct basisElement m)) = maskProduct vectorBasis m := by
  have h := map_maskProduct (e.toMonoidHom.comp projection) basisElement m
  change e (projection (maskProduct basisElement m)) = _ at h
  rw [show (fun i => (e.toMonoidHom.comp projection) (basisElement i)) = vectorBasis from
    funext he] at h
  exact h

theorem coordinateAction_eq (e : Coordinates) (he : RespectsBasis e)
    (g : localSubgroup) (masks : Fin 13 → ℕ) (u : QuotientMatrixˣ)
    (h : ∀ i, g⁻¹ * basis i * g = maskProduct basis (masks i))
    (hm : ∀ i, maskProduct vectorBasis (masks i) = rowAction u⁻¹ (vectorBasis i)) :
    coordinateAction e g = rowAction u := by
  have hh : e.toMonoidHom.comp (quotientAction g⁻¹).toMonoidHom =
      (rowAction u⁻¹).toMonoidHom.comp e.toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense quotientBasis_generate
    rintro q ⟨i, rfl⟩
    change e (quotientAction g⁻¹ (quotientBasis i)) = rowAction u⁻¹ (e (quotientBasis i))
    rw [quotientAction_basis_inv g masks h, coordinates_maskProduct e he, he, hm]
  have hi : coordinateAction e g⁻¹ = rowAction u⁻¹ := by
    apply MulEquiv.ext
    intro v
    obtain ⟨q, rfl⟩ := e.surjective v
    change e (quotientAction g⁻¹ (e.symm (e q))) = _
    rw [e.symm_apply_apply]
    exact DFunLike.congr_fun hh q
  rw [map_inv, map_inv] at hi
  exact inv_injective hi

theorem xMasks_coordinate_identity (i : Fin 13) :
    maskProduct vectorBasis (Certificates.xMasks i) = rowAction actionUnitX⁻¹ (vectorBasis i) := by
  revert i
  decide +kernel

theorem yMasks_coordinate_identity (i : Fin 13) :
    maskProduct vectorBasis (Certificates.yMasks i) = rowAction actionUnitY⁻¹ (vectorBasis i) := by
  revert i
  decide +kernel

theorem coordinateAction_x (e : Coordinates) (he : RespectsBasis e) :
    coordinateAction e subgroupX = rowAction actionUnitX :=
  coordinateAction_eq e he subgroupX Certificates.xMasks actionUnitX
    basis_action_x xMasks_coordinate_identity

theorem coordinateAction_y (e : Coordinates) (he : RespectsBasis e) :
    coordinateAction e subgroupY = rowAction actionUnitY :=
  coordinateAction_eq e he subgroupY Certificates.yMasks actionUnitY
    basis_action_y yMasks_coordinate_identity

attribute [local irreducible] rowAction canonicalRowAction coordinateAction

theorem quotientSubgroup_le_coordinateAction_range (e : Coordinates) (he : RespectsBasis e) :
    quotientSubgroup ≤ (coordinateAction e).range.comap canonicalRowAction := by
  apply (Subgroup.closure_le _).mpr
  intro u hu
  rcases hu with rfl | rfl
  · exact ⟨subgroupX, (coordinateAction_x e he).trans canonicalRowAction_x.symm⟩
  · exact ⟨subgroupY, (coordinateAction_y e he).trans canonicalRowAction_y.symm⟩

/-- Once the actual quotient coordinates are supplied, the literal matrix group
embeds into its action image and the outer-image comparison follows. -/
theorem card_comparison_of_coordinates (e : Coordinates) (he : RespectsBasis e) :
    Nat.card quotientSubgroup ≤ Nat.card localNormalClosureOuterAction.range := by
  let f : quotientSubgroup → (coordinateAction e).range := fun u =>
    ⟨canonicalRowAction u, quotientSubgroup_le_coordinateAction_range e he u.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact canonicalRowAction_injective (congrArg Subtype.val hab)
  have hfirst := Nat.card_le_card_of_injective f hf
  have hsecond : Nat.card (coordinateAction e).range ≤ Nat.card quotientAction.range :=
    range_card_le_of_ker_le quotientAction (coordinateAction e) (by
      intro g hg
      change coordinateAction e g = 1
      unfold coordinateAction
      change (MulAut.congr e) (quotientAction g) = 1
      rw [show quotientAction g = 1 from hg, map_one])
  exact hfirst.trans (hsecond.trans quotientAction_range_card_le_outerAction)

end OuterImageComparison
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
