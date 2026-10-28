module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.CoordinateMap
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.Extraspecial
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
/-!
# The intrinsic plus-type quadratic quotient

The coordinate homomorphism factors through `Q1/⟨k1⟩`, realized as the image
of `Q1` in `N/K`. Its remaining kernel is exactly the center. Thus the actual
central quotient is isomorphic to the twisted coordinate group of Exercise 4.6.
The word square and commutator identities identify its intrinsic quadratic and
polar forms, and the zero-code coordinates give a 12-dimensional totally
singular subspace in dimension 24. The final isometry and plus-type theorem
also apply to the literal quotient `Q1/⟨k1⟩`, whose central generator is the
image of `z1N`.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.4(2), pp. 61–62,
Exercise 4.6(1–3), p. 64, and the coordinate homomorphism in Section 27,
pp. 144–145. Both the all-ones and cocode-intersection corrections in the
source addition are retained.
-/

@[expose] public section
open Atlas.Fischer Atlas.Codes
open scoped commutatorElement
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

theorem Q1CentralKernel_eq_sup :
    Q1CentralKernel = Subgroup.zpowers z1N ⊔ K1 := by
  change Subgroup.closure {z1N,k1} = Subgroup.zpowers z1N ⊔ Subgroup.zpowers k1
  rw [Subgroup.zpowers_eq_closure,Subgroup.zpowers_eq_closure,
    ← Subgroup.closure_union,Set.singleton_union]

theorem q1ImageMap_kernel_le_coordinates : q1ImageMap.ker ≤ q1Coordinates.ker := by
  rw [q1ImageMap_ker,q1Coordinates_kernel]
  intro x hx
  exact (show K1 ≤ Q1CentralKernel by rw [Q1CentralKernel_eq_sup]; exact le_sup_right) hx

def q1ImageCoordinates : Q1Image →* Multiplicative QuadraticCoordinates :=
  q1ImageMap.liftOfSurjective q1ImageMap_surjective
    ⟨q1Coordinates,q1ImageMap_kernel_le_coordinates⟩

@[simp] theorem q1ImageCoordinates_apply (q : Q1) :
    q1ImageCoordinates (q1ImageMap q) = q1Coordinates q := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem q1ImageCoordinates_surjective : Function.Surjective q1ImageCoordinates := by
  intro x
  obtain ⟨q,rfl⟩ := q1Coordinates_surjective x
  exact ⟨q1ImageMap q,q1ImageCoordinates_apply q⟩

theorem Q1CentralKernel_image : Q1CentralKernel.map nQuotientMap =
    Subgroup.zpowers z1Image := by
  rw [Q1CentralKernel_eq_sup,Subgroup.map_sup,MonoidHom.map_zpowers]
  have hk : K1.map nQuotientMap = ⊥ := by
    rw [K1,MonoidHom.map_zpowers,(nQuotientMap_eq_one k1).mpr
      (K1_le_K (Subgroup.mem_zpowers k1)),Subgroup.zpowers_one_eq_bot]
  rw [hk,sup_bot_eq]
  rfl

theorem q1ImageCoordinates_kernel : q1ImageCoordinates.ker = Subgroup.center Q1Image := by
  have hc : q1ImageCoordinates.ker.comap q1ImageMap = q1Coordinates.ker := by
    ext q
    change q1ImageCoordinates (q1ImageMap q) = 1 ↔ q1Coordinates q = 1
    rw [q1ImageCoordinates_apply]
  have hm : q1ImageCoordinates.ker = q1Coordinates.ker.map q1ImageMap := by
    rw [← hc,Subgroup.map_comap_eq_self_of_surjective q1ImageMap_surjective]
  apply Subgroup.map_injective Q1Image.subtype_injective
  rw [hm,Q1Image_center,MonoidHom.map_zpowers]
  change (q1Coordinates.ker.map q1ImageMap).map Q1Image.subtype =
    Subgroup.zpowers z1Image
  rw [Subgroup.map_map]
  change q1Coordinates.ker.map (nQuotientMap.comp Q1.subtype) = _
  rw [← Subgroup.map_map,q1Coordinates_kernel_map,Q1CentralKernel_image]

/-- The central quotient of the actual extraspecial group. -/
abbrev Q1CentralQuotient := Q1Image ⧸ Subgroup.center Q1Image

def q1CentralCoordinatesEquiv : Q1CentralQuotient ≃* Multiplicative QuadraticCoordinates :=
  QuotientGroup.liftEquiv _ q1ImageCoordinates_surjective q1ImageCoordinates_kernel.symm

@[simp] theorem q1CentralCoordinatesEquiv_mk (q : Q1Image) :
    q1CentralCoordinatesEquiv (QuotientGroup.mk' (Subgroup.center Q1Image) q) =
      q1ImageCoordinates q := rfl

theorem Q1Image_square_coordinates (x : Q1Image) : x ^ 2 =
    q1ImageCenterGenerator ^ (coordinateQuadratic (q1ImageCoordinates x).toAdd).val := by
  obtain ⟨q,rfl⟩ := q1ImageMap_surjective x
  obtain ⟨⟨d,t,c⟩,rfl⟩ := q1Param_bijective.surjective q
  rw [q1ImageCoordinates_apply,q1Coordinates_param]
  apply Subtype.ext
  change nQuotientMap (q1Word d t c).val ^ 2 = nQuotientMap z1N ^ _
  rw [← map_pow,q1Word_sq,map_pow]
  rfl

instance q1CentralQuotientCommGroup : CommGroup Q1CentralQuotient :=
  q1CentralCoordinatesEquiv.toMonoidHom.commGroupOfInjective
    q1CentralCoordinatesEquiv.injective

instance q1CentralQuotientModule : Module Bit (Additive Q1CentralQuotient) :=
  (MulEquiv.toAdditiveLeft q1CentralCoordinatesEquiv).module Bit

/-- Coordinates preserve the quotient's group addition and its binary scalars. -/
def q1CentralCoordinatesLinearEquiv :
    Additive Q1CentralQuotient ≃ₗ[Bit] QuadraticCoordinates :=
  (MulEquiv.toAdditiveLeft q1CentralCoordinatesEquiv).linearEquiv Bit

/-- The square form on the central quotient, identified by the square law below. -/
def q1CentralQuadraticForm : QuadraticForm Bit (Additive Q1CentralQuotient) :=
  coordinateQuadraticForm.comp q1CentralCoordinatesLinearEquiv.toLinearMap

/-- Exercise 4.6(3): the coordinates give an isometry of the square form. -/
def q1CentralCoordinatesIsometry :
    q1CentralQuadraticForm.IsometryEquiv coordinateQuadraticForm :=
  { q1CentralCoordinatesLinearEquiv with map_app' := fun _ => rfl }

@[simp] theorem q1CentralQuadraticForm_apply (x : Additive Q1CentralQuotient) :
    q1CentralQuadraticForm x =
      coordinateQuadratic (q1CentralCoordinatesLinearEquiv x) := rfl

theorem q1CentralQuadraticForm_square (x : Q1Image) : x ^ 2 =
    q1ImageCenterGenerator ^ (q1CentralQuadraticForm
      (Additive.ofMul (QuotientGroup.mk' (Subgroup.center Q1Image) x))).val :=
  Q1Image_square_coordinates x

theorem q1CentralQuadraticForm_polar (x y : Additive Q1CentralQuotient) :
    q1CentralQuadraticForm.polarBilin x y =
      coordinatePolar (q1CentralCoordinatesLinearEquiv x)
        (q1CentralCoordinatesLinearEquiv y) := by
  rw [q1CentralQuadraticForm,QuadraticMap.polarBilin_comp,coordinateQuadraticForm_polar]
  rfl

theorem q1CentralQuadraticForm_nonsingular :
    q1CentralQuadraticForm.polarBilin.Nondegenerate := by
  constructor
  · intro x hx
    apply q1CentralCoordinatesLinearEquiv.injective
    rw [map_zero]
    apply coordinatePolar_separates
    intro y
    obtain ⟨y,rfl⟩ := q1CentralCoordinatesLinearEquiv.surjective y
    exact (q1CentralQuadraticForm_polar x y).symm.trans (hx y)
  · intro x hx
    apply q1CentralCoordinatesLinearEquiv.injective
    rw [map_zero]
    apply coordinatePolar_separates
    intro y
    obtain ⟨y,rfl⟩ := q1CentralCoordinatesLinearEquiv.surjective y
    rw [coordinatePolar_comm]
    exact (q1CentralQuadraticForm_polar y x).symm.trans (hx y)

theorem q1CentralQuotient_finrank :
    Module.finrank Bit (Additive Q1CentralQuotient) = 24 :=
  q1CentralCoordinatesLinearEquiv.finrank_eq.trans quadraticCoordinates_finrank

def q1CentralSingularSubspace : Submodule Bit (Additive Q1CentralQuotient) :=
  coordinateSingularSubspace.map q1CentralCoordinatesLinearEquiv.symm.toLinearMap

theorem q1CentralSingularSubspace_finrank :
    Module.finrank Bit q1CentralSingularSubspace = 12 := by
  rw [q1CentralSingularSubspace,LinearEquiv.finrank_map_eq,
    coordinateSingularSubspace_finrank]

theorem q1CentralSingularSubspace_totallySingular (x : Additive Q1CentralQuotient)
    (hx : x ∈ q1CentralSingularSubspace) : q1CentralQuadraticForm x = 0 := by
  obtain ⟨y,hy,rfl⟩ := hx
  change coordinateQuadratic
    (q1CentralCoordinatesLinearEquiv (q1CentralCoordinatesLinearEquiv.symm y)) = 0
  rw [LinearEquiv.apply_symm_apply]
  exact coordinateSingularSubspace_totallySingular y hy

theorem Q1Image_commutator_coordinates (x y : Q1Image) : ⁅x,y⁆ =
    q1ImageCenterGenerator ^ (coordinatePolar (q1ImageCoordinates x).toAdd
      (q1ImageCoordinates y).toAdd).val := by
  obtain ⟨a,rfl⟩ := q1ImageMap_surjective x
  obtain ⟨b,rfl⟩ := q1ImageMap_surjective y
  obtain ⟨⟨d,t,c⟩,rfl⟩ := q1Param_bijective.surjective a
  obtain ⟨⟨e,s,f⟩,rfl⟩ := q1Param_bijective.surjective b
  rw [q1ImageCoordinates_apply,q1ImageCoordinates_apply,
    q1Coordinates_param,q1Coordinates_param]
  apply Subtype.ext
  change ⁅nQuotientMap (q1Word d t c).val,nQuotientMap (q1Word e s f).val⁆ =
    nQuotientMap z1N ^ _
  rw [← map_commutatorElement,commutatorElement_def,q1Word_commutator,map_pow]
  rfl

/-- The actual extraspecial central quotient has the plus-type square form. -/
theorem Q1Image_plusType :
    IsExtraspecial 2 Q1Image ∧ Nat.card Q1Image = 2 ^ 25 ∧
    q1CentralQuadraticForm.polarBilin.Nondegenerate ∧
    Module.finrank Bit (Additive Q1CentralQuotient) = 24 ∧
    ∃ W : Submodule Bit (Additive Q1CentralQuotient), Module.finrank Bit W = 12 ∧
      ∀ x ∈ W, q1CentralQuadraticForm x = 0 :=
  ⟨Q1Image_extraspecial,Q1Image_card,q1CentralQuadraticForm_nonsingular,
    q1CentralQuotient_finrank,q1CentralSingularSubspace,
    q1CentralSingularSubspace_finrank,q1CentralSingularSubspace_totallySingular⟩

/-- The canonical identification also identifies the centers. -/
theorem q1QuotientEquivImage_map_center :
    (Subgroup.center Q1Quotient).map q1QuotientEquivImage.toMonoidHom =
      Subgroup.center Q1Image := by
  ext x
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (Subgroup.centerCongr q1QuotientEquivImage ⟨q,hq⟩).prop
  · intro hx
    exact ⟨q1QuotientEquivImage.symm x,
      (Subgroup.centerCongr q1QuotientEquivImage.symm ⟨x,hx⟩).prop,
      q1QuotientEquivImage.apply_symm_apply x⟩

abbrev Q1QuotientCentralQuotient := Q1Quotient ⧸ Subgroup.center Q1Quotient

def q1QuotientCentralEquiv : Q1QuotientCentralQuotient ≃* Q1CentralQuotient :=
  QuotientGroup.congr _ _ q1QuotientEquivImage q1QuotientEquivImage_map_center

@[simp] theorem q1QuotientCentralEquiv_mk (x : Q1Quotient) :
    q1QuotientCentralEquiv (QuotientGroup.mk' (Subgroup.center Q1Quotient) x) =
      QuotientGroup.mk' (Subgroup.center Q1Image) (q1QuotientEquivImage x) :=
  QuotientGroup.congr_mk' _ _ _ _ x

instance q1QuotientCentralQuotientCommGroup : CommGroup Q1QuotientCentralQuotient :=
  q1QuotientCentralEquiv.toMonoidHom.commGroupOfInjective q1QuotientCentralEquiv.injective

instance q1QuotientCentralQuotientModule :
    Module Bit (Additive Q1QuotientCentralQuotient) :=
  (MulEquiv.toAdditive q1QuotientCentralEquiv).module Bit

def q1QuotientCentralLinearEquiv :
    Additive Q1QuotientCentralQuotient ≃ₗ[Bit] Additive Q1CentralQuotient :=
  (MulEquiv.toAdditive q1QuotientCentralEquiv).linearEquiv Bit

def q1QuotientQuadraticForm : QuadraticForm Bit (Additive Q1QuotientCentralQuotient) :=
  q1CentralQuadraticForm.comp q1QuotientCentralLinearEquiv.toLinearMap

def q1QuotientCenterGenerator : Q1Quotient :=
  q1QuotientEquivImage.symm q1ImageCenterGenerator

@[simp] theorem q1QuotientEquivImage_mk (q : Q1) :
    q1QuotientEquivImage (QuotientGroup.mk' (K1.subgroupOf Q1) q) =
      q1ImageMap q := rfl

theorem q1QuotientCenterGenerator_eq_mk : q1QuotientCenterGenerator =
    QuotientGroup.mk' (K1.subgroupOf Q1) ⟨z1N,z1N_mem_Q1⟩ := by
  apply q1QuotientEquivImage.injective
  rw [q1QuotientCenterGenerator,MulEquiv.apply_symm_apply,q1QuotientEquivImage_mk]
  rfl

def q1QuotientCoordinatesIsometry :
    q1QuotientQuadraticForm.IsometryEquiv coordinateQuadraticForm :=
  { q1QuotientCentralLinearEquiv.trans q1CentralCoordinatesLinearEquiv with
    map_app' := fun _ => rfl }

theorem Q1Quotient_center : Subgroup.center Q1Quotient =
    Subgroup.zpowers q1QuotientCenterGenerator := by
  apply Subgroup.map_injective (f := q1QuotientEquivImage.toMonoidHom)
    q1QuotientEquivImage.injective
  rw [q1QuotientEquivImage_map_center,MonoidHom.map_zpowers,Q1Image_center]
  simp [q1QuotientCenterGenerator]

theorem q1QuotientQuadraticForm_square (x : Q1Quotient) : x ^ 2 =
    q1QuotientCenterGenerator ^ (q1QuotientQuadraticForm
      (Additive.ofMul (QuotientGroup.mk' (Subgroup.center Q1Quotient) x))).val := by
  apply q1QuotientEquivImage.injective
  rw [map_pow,map_pow,q1QuotientCenterGenerator,MulEquiv.apply_symm_apply]
  change q1QuotientEquivImage x ^ 2 =
    q1ImageCenterGenerator ^ (q1CentralQuadraticForm
      (Additive.ofMul (q1QuotientCentralEquiv
        (QuotientGroup.mk' (Subgroup.center Q1Quotient) x)))).val
  rw [q1QuotientCentralEquiv_mk]
  exact q1CentralQuadraticForm_square _

theorem q1QuotientQuadraticForm_nonsingular :
    q1QuotientQuadraticForm.polarBilin.Nondegenerate := by
  have h := LinearMap.BilinForm.Nondegenerate.congr
    (B := q1CentralQuadraticForm.polarBilin)
    q1QuotientCentralLinearEquiv.symm q1CentralQuadraticForm_nonsingular
  convert h using 1
  rw [q1QuotientQuadraticForm,QuadraticMap.polarBilin_comp]
  ext x y
  rfl

/-- Plus type for the literal quotient `Q1/⟨k1⟩`, with its group-square form. -/
theorem Q1Quotient_plusType :
    IsExtraspecial 2 Q1Quotient ∧ Nat.card Q1Quotient = 2 ^ 25 ∧
    q1QuotientQuadraticForm.polarBilin.Nondegenerate ∧
    Module.finrank Bit (Additive Q1QuotientCentralQuotient) = 24 ∧
    ∃ W : Submodule Bit (Additive Q1QuotientCentralQuotient), Module.finrank Bit W = 12 ∧
      ∀ x ∈ W, q1QuotientQuadraticForm x = 0 := by
  refine ⟨Q1Quotient_extraspecial,Q1Quotient_card,q1QuotientQuadraticForm_nonsingular,
    q1QuotientCentralLinearEquiv.finrank_eq.trans q1CentralQuotient_finrank,
    q1CentralSingularSubspace.map q1QuotientCentralLinearEquiv.symm.toLinearMap,?_,?_⟩
  · rw [LinearEquiv.finrank_map_eq,q1CentralSingularSubspace_finrank]
  · rintro x ⟨y,hy,rfl⟩
    change q1CentralQuadraticForm
      (q1QuotientCentralLinearEquiv (q1QuotientCentralLinearEquiv.symm y)) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact q1CentralSingularSubspace_totallySingular y hy

end Sporadic.Monster.Construction.TrialitySpin
