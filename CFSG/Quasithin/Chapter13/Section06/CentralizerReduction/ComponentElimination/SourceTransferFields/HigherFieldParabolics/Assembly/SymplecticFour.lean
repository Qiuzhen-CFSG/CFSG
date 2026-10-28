module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.Normalizers

/-!
# Literal plus-model preimages for the remaining Sp₄ branch

The source model identifies K⁺ with the matrix group Sp₄(F). Pull back the
two standard parabolics along K → K⁺ → Sp₄(F); no identification of K itself
with Sp₄ is imposed. Their residuals have precisely the point and plane
local images, giving the required literal PSL₂ plus-core quotients. The
parabolics are maximal relative to K, and a Sylow marking places Tᵥ ∩ K
inside both.

These shared constructions leave the marked-module obstruction and local
geometry to their independent source proofs. In particular the matrix
residuals being blocks does not prove that their source preimages are blocks
or non-blocks. No intrinsic core quotient or invariance is inferred here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.19,
printed p.931, and F.1.12(I)(2), printed pp.262–264.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour
open ComponentSelection
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable {F : Type*} [Field F]
variable (e : plusImage K L T z v hL hz K ≃* Sp F)

/-- The actual component quotient map, followed by the source model. -/
def modelMap : K →* Sp F :=
  e.toMonoidHom.comp (LinearThree.componentPlusMap K L T z v hL hz)

theorem modelMap_surjective : Function.Surjective (modelMap K L T z v hL hz e) :=
  e.surjective.comp (LinearThree.componentPlusMap_surjective K L T z v hL hz)

theorem modelMap_ker : (modelMap K L T z v hL hz e).ker =
    (centralizer (WK K L T z v : Set G)).subgroupOf K := by
  rw [modelMap, MonoidHom.ker_comp_of_injective _ _ e.injective,
    LinearThree.componentPlusMap_ker]

/-- The full point parabolic in the original source group. -/
noncomputable def pointPreimage : Subgroup G :=
  LinearThree.preimageIn K (modelMap K L T z v hL hz e) pointParabolic

/-- The full plane parabolic in the original source group. -/
noncomputable def planePreimage : Subgroup G :=
  LinearThree.preimageIn K (modelMap K L T z v hL hz e) planeParabolic

theorem pointPreimage_le : pointPreimage K L T z v hL hz e ≤ K := map_subtype_le _

theorem planePreimage_le : planePreimage K L T z v hL hz e ≤ K := map_subtype_le _

variable [Finite F]

/-- Maximality is relative to K, including the literal action kernel. -/
theorem pointPreimage_maximal :
    IsCoatom ((pointPreimage K L T z v hL hz e).subgroupOf K) := by
  change IsCoatom (((pointParabolic.comap (modelMap K L T z v hL hz e)).map
    K.subtype).comap K.subtype)
  rw [comap_map_eq_self_of_injective K.subtype_injective]
  exact isCoatom_comap_of_surjective (modelMap_surjective K L T z v hL hz e)
    BorelActionGeometry.pointParabolic_isCoatom

variable [CharP F 2]

theorem planePreimage_maximal :
    IsCoatom ((planePreimage K L T z v hL hz e).subgroupOf K) := by
  change IsCoatom (((planeParabolic.comap (modelMap K L T z v hL hz e)).map
    K.subtype).comap K.subtype)
  rw [comap_map_eq_self_of_injective K.subtype_injective]
  exact isCoatom_comap_of_surjective (modelMap_surjective K L T z v hL hz e)
    BorelActionGeometry.planeParabolic_isCoatom

omit [Finite F] [CharP F 2] in
/-- The marked Sylow intersection lies in both original parabolic preimages. -/
theorem marked_intersection_le
    (hmark : ((Tv T v).subgroupOf K).map (modelMap K L T z v hL hz e) ≤ unipotent) :
    Tv T v ⊓ K ≤ pointPreimage K L T z v hL hz e ∧
      Tv T v ⊓ K ≤ planePreimage K L T z v hL hz e := by
  constructor
  · intro x hx
    exact ⟨⟨x, hx.2⟩, (unipotent_le_borel.trans inf_le_left)
      (hmark (mem_map_of_mem _ hx.1)), rfl⟩
  · intro x hx
    exact ⟨⟨x, hx.2⟩, (unipotent_le_borel.trans inf_le_right)
      (hmark (mem_map_of_mem _ hx.1)), rfl⟩

variable [Finite G] {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 < m)

include hF hm in
/-- The literal point residual maps onto the point determinant kernel. -/
theorem point_residual_image :
    ((residualIn (pointPreimage K L T z v hL hz e)).subgroupOf K).map
      (modelMap K L T z v hL hz e) = pointLocal :=
  (LinearThree.residualIn_preimage_image K _
    (modelMap_surjective K L T z v hL hz e) pointParabolic).trans
      (pointParabolic_solvableResidual_eq hF hm)

include hF hm in
theorem plane_residual_image :
    ((residualIn (planePreimage K L T z v hL hz e)).subgroupOf K).map
      (modelMap K L T z v hL hz e) = planeLocal :=
  (LinearThree.residualIn_preimage_image K _
    (modelMap_surjective K L T z v hL hz e) planeParabolic).trans
      (planeParabolic_solvableResidual_eq hF hm)

/-- Identification of the actual plus image, before removing its two-core. -/
noncomputable def pointPlusEquiv :
    plusImage K L T z v hL hz (residualIn (pointPreimage K L T z v hL hz e)) ≃*
      pointLocal (F := F) :=
  (LinearThree.plusResidualEquiv K L T z v hL hz e pointParabolic).trans
    (MulEquiv.subgroupCongr (pointParabolic_solvableResidual_eq hF hm))

noncomputable def planePlusEquiv :
    plusImage K L T z v hL hz (residualIn (planePreimage K L T z v hL hz e)) ≃*
      planeLocal (F := F) :=
  (LinearThree.plusResidualEquiv K L T z v hL hz e planeParabolic).trans
    (MulEquiv.subgroupCongr (planeParabolic_solvableResidual_eq hF hm))

/-- Source 13.6.19's literal K₁⁺/O₂(K₁⁺) in the point case. -/
noncomputable def pointPlusCoreEquiv :
    (plusImage K L T z v hL hz (residualIn (pointPreimage K L T z v hL hz e)) ⧸
      pCore 2 (plusImage K L T z v hL hz
        (residualIn (pointPreimage K L T z v hL hz e)))) ≃* PSL(2, F) :=
  let a := pointPlusEquiv K L T z v hL hz e hF hm
  (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    ((pointLocalCoreQuotientEquiv hF hm).trans (Theory.PSL2.sl2QuotientEquiv F))

/-- Source 13.6.19's literal K₁⁺/O₂(K₁⁺) in the plane case. -/
noncomputable def planePlusCoreEquiv :
    (plusImage K L T z v hL hz (residualIn (planePreimage K L T z v hL hz e)) ⧸
      pCore 2 (plusImage K L T z v hL hz
        (residualIn (planePreimage K L T z v hL hz e)))) ≃* PSL(2, F) :=
  let a := planePlusEquiv K L T z v hL hz e hF hm
  (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    ((planeLocalCoreQuotientEquiv hF hm).trans (Theory.PSL2.sl2QuotientEquiv F))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour
