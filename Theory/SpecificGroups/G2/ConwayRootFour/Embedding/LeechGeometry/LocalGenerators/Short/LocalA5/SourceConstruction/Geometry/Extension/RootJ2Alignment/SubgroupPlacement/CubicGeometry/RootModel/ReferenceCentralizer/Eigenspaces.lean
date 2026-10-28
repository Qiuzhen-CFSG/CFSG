module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.Reference
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Scalar
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.Relations
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The reference cubic's intrinsic eigenspace action

Restrict the full ambient common centralizer to the literal U-fixed space,
with the F₄ scalar structure furnished by the actual tetrahedral element Y.
Commutation with the reference cubic preserves its eigenspaces. The retained
ATLAS involution x inverts the reference commutator fourth power, so its
F₄-linear action exchanges the two nontrivial eigenspaces. They are disjoint
and have equal dimension; the existing dimension-six bound therefore bounds
each by three.

This constructs an actual action without a long frame, carrier comparison,
or cubic-fusion hypothesis. Faithfulness on one eigenspace and its determinant
are not asserted here. `Coordinates` uses the bound to make a three-dimensional
matrix action, with precisely those two remaining geometric obligations.

Source: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and the action in
49.5, p.283. The concrete ATLAS pair and the icosian scalar models retain their
attribution and license in the imported modules and `LICENSES/ATLAS.txt`.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
local notation "Gen" => Sporadic.LeechRelated.J2.IcosianComparison.Generators.x

/-- The actual projective ATLAS involution, inside the same scalar centralizer. -/
def referenceInverter : LeechCentralQuotient := icosianProjectiveToCo1 Gen

theorem referenceInverter_mem : referenceInverter ∈ centralizerI := janko_mem_centralizerI _

theorem referenceInverter_square : referenceInverter ^ 2 = 1 := by
  have h := Sporadic.LeechRelated.J2.IcosianComparison.Generators.relations (0 : Fin 5)
  change Gen ^ 2 = 1 at h
  rw [referenceInverter, ← map_pow, h, map_one]

theorem referenceInverter_conjugate :
    referenceInverter * referenceCubic * referenceInverter⁻¹ = referenceCubic⁻¹ := by
  have hx : Gen ^ 2 = 1 :=
    Sporadic.LeechRelated.J2.IcosianComparison.Generators.relations (0 : Fin 5)
  have hxi : Gen⁻¹ = Gen := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
  have hc : MulAut.conj Gen
      (Gen⁻¹ * Sporadic.LeechRelated.J2.IcosianComparison.Generators.y⁻¹ * Gen *
        Sporadic.LeechRelated.J2.IcosianComparison.Generators.y) =
      (Gen⁻¹ * Sporadic.LeechRelated.J2.IcosianComparison.Generators.y⁻¹ * Gen *
        Sporadic.LeechRelated.J2.IcosianComparison.Generators.y)⁻¹ := by
    simp only [MulAut.conj_apply, mul_assoc, mul_inv_cancel_left,
      _root_.mul_inv_rev, inv_inv]
    rw [hxi]
  have hp : referenceProjective =
      (Gen⁻¹ * Sporadic.LeechRelated.J2.IcosianComparison.Generators.y⁻¹ * Gen *
        Sporadic.LeechRelated.J2.IcosianComparison.Generators.y) ^ 4 := by
    simp only [referenceProjective, referenceLift, map_pow, map_mul, map_inv]
    rfl
  have hh : MulAut.conj Gen referenceProjective = referenceProjective⁻¹ := by
    rw [hp, map_pow, hc, inv_pow]
  simpa only [referenceInverter, referenceCubic, MulAut.conj_apply, map_mul, map_inv] using
    congrArg icosianProjectiveToCo1 hh

/-- A specified nontrivial cubic root in the existing field of four elements. -/
def referenceScalar : F := Long.scalarFieldEquiv.symm goldenFourTau

theorem referenceScalar_cube : referenceScalar ^ 3 = 1 := by
  apply Long.scalarFieldEquiv.injective
  simp only [map_pow, referenceScalar, RingEquiv.apply_symm_apply, map_one]
  decide +kernel

theorem referenceScalar_ne_zero : referenceScalar ≠ 0 := by
  intro h
  have := referenceScalar_cube
  rw [h, zero_pow (by decide)] at this
  exact zero_ne_one this

theorem referenceScalar_ne_inv : referenceScalar ≠ referenceScalar⁻¹ := by
  intro h
  have h' := congrArg Long.scalarFieldEquiv h
  simp only [referenceScalar, map_inv₀, RingEquiv.apply_symm_apply] at h'
  exact (by decide +kernel : goldenFourTau ≠ goldenFourTau⁻¹) h'

/-- The reference cubic on the literal U-fixed space. -/
def referenceOperator : fixedSpace ≃ₗ[F] fixedSpace :=
  Long.centralizerAction ⟨referenceCubic, referenceCubic_mem⟩

/-- An eigenspace in the fixed space, with its published F₄ structure. -/
def referenceEigenspace (a : F) : Submodule F fixedSpace :=
  Module.End.eigenspace referenceOperator.toLinearMap a

theorem mem_referenceEigenspace (a : F) (v : fixedSpace) :
    v ∈ referenceEigenspace a ↔ referenceOperator v = a • v :=
  Module.End.mem_eigenspace_iff

/-- Restriction of the full ambient common centralizer, not a generated subgroup. -/
def referenceFixedAction : referenceCentralizer →* (fixedSpace ≃ₗ[F] fixedSpace) :=
  Long.centralizerAction.comp (Subgroup.inclusion inf_le_left)

theorem referenceFixedAction_commute (g : referenceCentralizer) :
    Commute referenceOperator (referenceFixedAction g) := by
  apply Commute.map
  apply Subtype.ext
  change referenceCubic * g.val = g.val * referenceCubic
  exact g.property.2 referenceCubic (Subgroup.mem_zpowers referenceCubic)

theorem referenceFixedAction_preserves (g : referenceCentralizer) (a : F)
    {v : fixedSpace} (hv : v ∈ referenceEigenspace a) :
    referenceFixedAction g v ∈ referenceEigenspace a := by
  rw [mem_referenceEigenspace] at hv ⊢
  calc
    referenceOperator (referenceFixedAction g v) =
      referenceFixedAction g (referenceOperator v) :=
        DFunLike.congr_fun (referenceFixedAction_commute g).eq v
    _ = a • referenceFixedAction g v := by rw [hv, map_smul]

/-- The actual F₄-linear action on each reference eigenspace. -/
def referenceEigenAction (a : F) :
    referenceCentralizer →* (referenceEigenspace a ≃ₗ[F] referenceEigenspace a) where
  toFun g :=
    { toFun v := ⟨referenceFixedAction g v, referenceFixedAction_preserves g a v.property⟩
      invFun v := ⟨referenceFixedAction g⁻¹ v, referenceFixedAction_preserves g⁻¹ a v.property⟩
      left_inv := by intro v; apply Subtype.ext; simp
      right_inv := by intro v; apply Subtype.ext; simp
      map_add' := by intro v w; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c v; apply Subtype.ext; exact map_smul _ _ _ }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    exact DFunLike.congr_fun (map_one referenceFixedAction) v.val
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    exact DFunLike.congr_fun (map_mul referenceFixedAction g h) v.val

@[simp] theorem referenceEigenAction_apply (a : F) (g : referenceCentralizer)
    (v : referenceEigenspace a) :
    (referenceEigenAction a g v).val.val = quotientModTwoRepresentation g.val v.val.val := rfl

/-- The ATLAS inverter acts linearly because it centralizes the same I. -/
def referenceSwap : fixedSpace ≃ₗ[F] fixedSpace :=
  Long.centralizerAction ⟨referenceInverter, referenceInverter_mem⟩

theorem referenceSwap_square (v : fixedSpace) : referenceSwap (referenceSwap v) = v := by
  have hs : (⟨referenceInverter, referenceInverter_mem⟩ : centralizerI) ^ 2 = 1 :=
    Subtype.ext referenceInverter_square
  have h := congrArg Long.centralizerAction hs
  rw [map_pow, map_one, pow_two] at h
  exact DFunLike.congr_fun h v

theorem referenceSwap_relation (v : fixedSpace) :
    referenceOperator (referenceSwap v) = referenceSwap (referenceOperator.symm v) := by
  have hc : referenceCubic * referenceInverter = referenceInverter * referenceCubic⁻¹ := by
    have hi : referenceInverter⁻¹ = referenceInverter :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using referenceInverter_square)
    have h := referenceInverter_conjugate
    rw [hi] at h
    calc
      referenceCubic * referenceInverter =
          referenceInverter * (referenceInverter * referenceCubic * referenceInverter) := by
            have hs := referenceInverter_square
            rw [pow_two] at hs
            simp only [← mul_assoc, hs, one_mul]
      _ = referenceInverter * referenceCubic⁻¹ := by rw [h]
  have hs : (⟨referenceCubic, referenceCubic_mem⟩ : centralizerI) *
      ⟨referenceInverter, referenceInverter_mem⟩ =
      ⟨referenceInverter, referenceInverter_mem⟩ *
      (⟨referenceCubic, referenceCubic_mem⟩ : centralizerI)⁻¹ := Subtype.ext hc
  have h := congrArg Long.centralizerAction hs
  simp only [map_mul, map_inv] at h
  exact DFunLike.congr_fun h v

theorem referenceSwap_eigen {a : F} (ha : a ≠ 0) {v : fixedSpace}
    (hv : v ∈ referenceEigenspace a) :
    referenceSwap v ∈ referenceEigenspace a⁻¹ := by
  rw [mem_referenceEigenspace] at hv ⊢
  have hinv : referenceOperator.symm v = a⁻¹ • v := by
    apply referenceOperator.injective
    rw [LinearEquiv.apply_symm_apply, map_smul, hv, smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [referenceSwap_relation, hinv, map_smul]

/-- The explicit inverter exchanges the two nontrivial eigenspaces. -/
def referenceEigenspaceSwap :
    referenceEigenspace referenceScalar ≃ₗ[F] referenceEigenspace referenceScalar⁻¹ where
  toFun v := ⟨referenceSwap v, referenceSwap_eigen referenceScalar_ne_zero v.property⟩
  invFun v := ⟨referenceSwap v, by
    simpa only [inv_inv] using
      referenceSwap_eigen (inv_ne_zero referenceScalar_ne_zero) v.property⟩
  left_inv := by intro v; apply Subtype.ext; exact referenceSwap_square v
  right_inv := by intro v; apply Subtype.ext; exact referenceSwap_square v
  map_add' := by intro v w; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intro c v; apply Subtype.ext; exact map_smul _ _ _

/-- Equal, disjoint eigenspaces inside at most six dimensions have dimension at most three. -/
theorem referenceEigenspace_finrank_le_three :
    Module.finrank F (referenceEigenspace referenceScalar) ≤ 3 := by
  have hd : Disjoint (referenceEigenspace referenceScalar)
      (referenceEigenspace referenceScalar⁻¹) :=
    (Module.End.eigenspaces_iSupIndep referenceOperator.toLinearMap).pairwiseDisjoint
      referenceScalar_ne_inv
  have h := Submodule.finrank_add_finrank_le_of_disjoint hd
  have he := referenceEigenspaceSwap.finrank_eq
  have h6 := Long.fixedSpace_finrank_le_six
  omega

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
