module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ActionModel.Outer
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.SourceModel

/-!
# Construction of the marked H.9 model on the actual action quotient

The original coordinates give complementary natural and dual summands.
The component-layer marking and the proved outer interchange supply the
H.9 source setup. Its quadratic form agrees with the supplied evaluation
form: after transport through the original coordinates, inner invariance,
singular summands, and nondegeneracy characterize the evaluation form.

The resulting SourceModel retains the literal quotient representation,
component map, both summands, and quadratic form without extra premises.
Source: Aschbacher--Smith, H.9.1 and 12.1, printed pp.389--390,788.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryNaturalDual BinaryLinear.OuterCyclic
open BinaryNaturalDual.ModelOrbits
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

def naturalCoordinates : B.naturalSpace ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n where
  toFun u := (B.linearCoordinates u).1
  invFun x := ⟨B.linearCoordinates.symm (x, 0), by
    change (B.linearCoordinates (B.linearCoordinates.symm (x, 0))).2 = 0
    rw [B.linearCoordinates.apply_symm_apply]⟩
  left_inv u := by
    apply Subtype.ext
    apply B.linearCoordinates.injective
    rw [B.linearCoordinates.apply_symm_apply]
    exact Prod.ext rfl (show (B.linearCoordinates u).2 = 0 from u.property).symm
  right_inv x := by simp only [B.linearCoordinates.apply_symm_apply]
  map_add' x y := by simp only [Submodule.coe_add, map_add, Prod.fst_add]
  map_smul' c x := by
    simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
    rfl

theorem natural_dual_complement : IsCompl B.naturalSpace B.dualSpace := by
  change IsCompl ((Submodule.orderIsoMapComap B.linearCoordinates).symm
    (LinearMap.snd (ZMod 2) (BinaryLinear.OuterCyclic.Space n) _).ker)
    ((Submodule.orderIsoMapComap B.linearCoordinates).symm
    (LinearMap.fst (ZMod 2) (BinaryLinear.OuterCyclic.Space n) _).ker)
  rw [← (Submodule.orderIsoMapComap B.linearCoordinates).symm.isCompl_iff,
    LinearMap.ker_snd, LinearMap.ker_fst]
  exact LinearMap.isCompl_range_inl_inr

def quotientSourceSetup : ChapterH.NaturalDual.SourceSetup n B.ActionQuotient
    (Additive (componentOrbit V (T : Subgroup G))) where
  degree := B.degree
  projective := B.full.trans
    (AutomorphismModel.projectiveAutEquiv (by have := B.degree; omega)).symm
  layer := B.quotientLayerEquiv
  representation := B.quotientRepresentation
  natural := B.naturalSpace
  dual := B.dualSpace
  complement := B.natural_dual_complement
  naturalCoordinates := B.naturalCoordinates
  natural_action := by
    intro l x
    apply B.linearCoordinates.injective
    rw [B.quotientLayerEquiv_coordinates]
    change naturalDualRepresentation (B.quotientLayerEquiv l)
      (B.linearCoordinates (B.linearCoordinates.symm (x, 0))) =
      B.linearCoordinates (B.linearCoordinates.symm (B.quotientLayerEquiv l x, 0))
    simp only [B.linearCoordinates.apply_symm_apply, naturalDualRepresentation_apply, map_zero]
  outer := B.exists_quotient_outer

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

theorem quotientSourceSetup_quadratic : B.quotientSourceSetup.quadratic = B.quadratic := by
  let S := B.quotientSourceSetup
  let Q := S.quadratic.comp B.linearCoordinates.symm.toLinearMap
  have h₁ (x : BinaryLinear.OuterCyclic.Space n) : Q (x, 0) = 0 := by
    apply S.quadratic_invariant.2.1
    change (B.linearCoordinates (B.linearCoordinates.symm (x, 0))).2 = 0
    rw [B.linearCoordinates.apply_symm_apply]
  have h₂ (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) : Q (0, f) = 0 := by
    have hv : B.linearCoordinates.symm (0, f) ∈ S.dual := by
      change (B.linearCoordinates (B.linearCoordinates.symm (0, f))).1 = 0
      rw [B.linearCoordinates.apply_symm_apply]
    change S.quadratic (B.linearCoordinates.symm (0, f)) = 0
    rw [S.quadratic_apply, S.model.dual_marking ⟨_, hv⟩]
    simp only [BinaryNaturalDual.quadratic_apply, map_zero]
  have hQ (g : LinearGroup n) (v : CoordinateSpace n) :
      Q (naturalDualRepresentation g v) = Q v := by
    have he := B.quotientLayerEquiv_coordinates (B.quotientLayerEquiv.symm g)
      (B.linearCoordinates.symm v)
    rw [B.quotientLayerEquiv.apply_symm_apply, B.linearCoordinates.apply_symm_apply] at he
    have ht : B.linearCoordinates.symm (naturalDualRepresentation g v) =
        B.quotientRepresentation (B.quotientLayerEquiv.symm g)
          (B.linearCoordinates.symm v) := by
      apply B.linearCoordinates.injective
      rw [B.linearCoordinates.apply_symm_apply, he]
    change S.quadratic (B.linearCoordinates.symm (naturalDualRepresentation g v)) =
      S.quadratic (B.linearCoordinates.symm v)
    rw [ht]
    exact S.quadratic_invariant.2.2 _ _
  have hnd : Q.polarBilin.Nondegenerate := by
    rw [show Q = S.quadratic.comp B.linearCoordinates.symm.toLinearMap from rfl,
      QuadraticMap.polarBilin_comp]
    constructor
    · intro x hx
      apply B.linearCoordinates.symm.injective
      rw [map_zero]
      apply S.quadratic_invariant.1.1
      intro y
      obtain ⟨z, rfl⟩ := B.linearCoordinates.symm.surjective y
      exact hx z
    · intro x hx
      apply B.linearCoordinates.symm.injective
      rw [map_zero]
      apply S.quadratic_invariant.1.2
      intro y
      obtain ⟨z, rfl⟩ := B.linearCoordinates.symm.surjective y
      exact hx z
  have he := BinaryNaturalDual.ModelOrbits.quadratic_unique Q h₁ h₂ hQ hnd
  ext w
  have ht := congrArg (fun q : QuadraticForm (ZMod 2) (CoordinateSpace n) =>
    q (B.linearCoordinates w)) he
  change S.quadratic (B.linearCoordinates.symm (B.linearCoordinates w)) = _ at ht
  change S.quadratic w = BinaryNaturalDual.quadratic (B.linearCoordinates w)
  simpa only [B.linearCoordinates.symm_apply_apply] using ht

omit [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))] in
theorem componentToActionQuotient_range_eq_layer :
    B.componentToActionQuotient.range = componentLayer B.ActionQuotient := by
  rw [← B.componentEmbedding_range_eq_layer]
  ext a
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨QuotientGroup.mk' (pCore 2 L) l, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    exact ⟨l, rfl⟩

def sourceModel : B.SourceModel where
  setup := B.quotientSourceSetup
  representation_eq := rfl
  component_layer := B.componentToActionQuotient_range_eq_layer
  layer_marking l := B.quotientLayerEquiv_embedding (QuotientGroup.mk' (pCore 2 L) l)
  natural_marking _ := Iff.rfl
  dual_marking _ := Iff.rfl
  quadratic_eq := B.quotientSourceSetup_quadratic

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
