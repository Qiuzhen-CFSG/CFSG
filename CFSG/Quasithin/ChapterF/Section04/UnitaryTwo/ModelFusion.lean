module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourProjectiveInvolutionPlacement
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PlaneParabolic

/-!
# Model fusion on the binary unitary plane radical

In the actual projective U₄(2) group the plane radical is the elementary
Thompson subgroup of the marked upper Sylow. Its normalizer is exactly the
plane parabolic, since its fixed vectors form the original coordinate plane.
Burnside fusion therefore replaces any ambient conjugator of two radical
elements by an element of that same parabolic.

These are the concrete-model fusion inputs for the ordinary branch of
Aschbacher--Smith F.4.35, printed pp.291--292.
-/
@[expose] public noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.ModelFusion
open GreenBook.LieModels.UnitaryFour
open InvolutionPlacement
open Theory.SpecificGroups.ClassicalUnitary
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => L2 1 hn

private theorem matrix_core_eq_ambientRadical :
    (pCore 2 (L2Matrix 1 hn)).map (L2Matrix 1 hn).subtype =
      UnitaryFourConverse.PlaneParabolic.ambientRadical F σ hσ := by
  rw [← L2MatrixRadical_eq_twoCore]
  apply le_antisymm
  · rintro x ⟨a, ha, rfl⟩
    let q := (UnitaryFourConverse.PlaneParabolic.kernelEquivRadical F σ hσ).symm
      ⟨a, ha⟩
    exact ⟨q.val, q.property, rfl⟩
  · rintro x ⟨a, ha, rfl⟩
    let q := UnitaryFourConverse.PlaneParabolic.kernelEquivRadical F σ hσ
      ⟨a, ha⟩
    exact ⟨q.val, q.property, rfl⟩

/-- The normalizer is the original full plane endpoint. -/
theorem planeCore_normalizer :
    normalizer (planeCore : Set (ProjectiveGroup 1 hn)) = planeParabolic 1 hn := by
  have hm : normalizer (((pCore 2 (L2Matrix 1 hn)).map
      (L2Matrix 1 hn).subtype : Subgroup (MatrixGroup 1 hn)) : Set _) =
      planeParabolicMatrix 1 hn := by
    rw [matrix_core_eq_ambientRadical]
    exact UnitaryFourConverse.PlaneParabolic.normalizer_ambientRadical F σ hσ
  rw [← matrix_plane_core_map, ← Subgroup.map_normalizer_eq_of_bijective _
    ⟨projection_injective 1 hn, UnitaryFourFlag.project_surjective F (standardForm 1 hn)⟩, hm]
  rfl

/-- The same marked upper Sylow has the plane radical as its Thompson subgroup. -/
theorem projective_thompson :
    elementaryAbelianMaxJ (projectiveSylow 1 hn : Subgroup _) = planeCore := by
  have hs : (PlainFusion.localSylow : Subgroup L).map (L2 1 hn).subtype =
      (projectiveSylow 1 hn : Subgroup _) := by
    apply le_antisymm
    · rintro x ⟨a, ha, rfl⟩
      exact ha
    · intro x hx
      exact ⟨⟨x, PlainFusion.sylow_le_local hx⟩, hx, rfl⟩
  rw [← hs, elementaryAbelianMaxJ_map_injective _ Subtype.val_injective,
    PlaneThompson.plane_thompson]
  rfl

/-- Every model fusion between plane-radical elements occurs in the marked
plane parabolic. -/
theorem plane_fusion {x y : ProjectiveGroup 1 hn}
    (hx : x ∈ planeCore) (hy : y ∈ planeCore) (hxy : IsConj x y) :
    ∃ p : planeParabolic 1 hn, p.val * x * p.val⁻¹ = y := by
  let : IsElementaryAbelian 2 planeCore := IsElementaryAbelian.map (L2 1 hn).subtype
  have hVS : planeCore ≤ (projectiveSylow 1 hn : Subgroup _) := by
    rw [← projective_thompson]
    exact sSup_le fun A hA => hA.1
  have hweak : ∀ g : ProjectiveGroup 1 hn,
      planeCore.conjBy g ≤ (projectiveSylow 1 hn : Subgroup _) →
      planeCore.conjBy g = planeCore := by
    intro g hg
    change planeCore.map (MulAut.conj g).toMonoidHom ≤
      (projectiveSylow 1 hn : Subgroup _) at hg
    change planeCore.map (MulAut.conj g).toMonoidHom = planeCore
    have hh := elementaryAbelianMaxJ_map_eq_of_le
      (projectiveSylow 1 hn : Subgroup _) (MulAut.conj g)
      (by rwa [projective_thompson])
    simpa only [projective_thompson] using hh
  obtain ⟨n, hnN, he⟩ :=
    (projectiveSylow 1 hn).normalizer_fuses_of_abelian_weakly_closed
      planeCore hVS hweak hx hy hxy
  exact ⟨⟨n, planeCore_normalizer ▸ hnN⟩, he⟩

end CFSG.Quasithin.ChapterF.UnitaryTwo.ModelFusion
