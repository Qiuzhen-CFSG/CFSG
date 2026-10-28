module
public import Theory.SpecificGroups.SL2.NoLinearThreeSection
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals

/-!
# Linear-three two-core sections in binary rank-two parabolics

A perfect subgroup of a symplectic or G₂ parabolic lies in its local
residual. The residual maps to binary SL₂ with a two-group kernel.
The order-four obstruction in PSL₃(2) therefore excludes a map with
solvable kernel from a perfect PSL₃(2) two-core extension. Applying the
actual full-Sylow parabolic covers excludes every proper Sylow overgroup
containing such an image. The original two-core extension need not split.

Source: the classical enlargement comparison in Aschbacher–Smith,
Lemma 12.3.3, printed p.808. The G₂ model and local calculations retain
the ATLAS attribution in their imports; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
variable {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
namespace Theory.SpecificGroups.SymplecticFour

omit [Finite B] [Finite F] [CharP F 2] in
private theorem perfect_image_local
    (f : B →* Sp F) (W : Submodule F (Vector F)) (hf : f.range ≤ stabilizer W) :
    f.range ≤ determinantKernel W := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  exact (le_map_solvableResidual_of_isPerfect f.range (stabilizer W) hf).trans
    (determinantKernel_solvableResidual_le W)

theorem no_linearThree_section_in_parabolic
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (f : B →* Sp F) [Group.IsSolvable f.ker]
    (hp : f.range ≤ pointParabolic ∨ f.range ≤ planeParabolic) : False := by
  rcases hp with hp | hp
  · have hl : f.range ≤ pointLocal := perfect_image_local f (point F) hp
    let j := f.codRestrict pointLocal (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let : Group.IsSolvable (pointQuotient (F := F)).ker := by
      rw [pointQuotient_ker]
      let : Group.IsNilpotent (pointRadical (F := F)) :=
        (IsElementaryAbelian.isPGroup 2 _).isNilpotent
      infer_instance
    exact Matrix.PSL3Two.no_solvable_kernel_rankOne_local e j pointQuotient
  · have hl : f.range ≤ planeLocal := perfect_image_local f (plane F) hp
    let j := f.codRestrict planeLocal (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let : Group.IsSolvable (Plane.quotientMap (F := F)).ker := by
      rw [Plane.quotientMap_ker]
      let : Group.IsNilpotent (Plane.radical (F := F)) :=
        (IsElementaryAbelian.isPGroup 2 _).isNilpotent
      infer_instance
    exact Matrix.PSL3Two.no_solvable_kernel_rankOne_local e j Plane.quotientMap

theorem linearThree_section_sylow_overgroup_eq_top
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (hF : 2 < Nat.card F) (P : Sylow 2 (Sp F)) (D : Subgroup (Sp F))
    (hPD : (P : Subgroup (Sp F)) ≤ D)
    (f : B →* Sp F) [Group.IsSolvable f.ker] (hBD : f.range ≤ D) : D = ⊤ := by
  by_contra hD
  obtain ⟨g,hg⟩ := ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover hF P D hPD hD
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hk : j.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
  have hj : j.range ≤ D.map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono hBD
  exact no_linearThree_section_in_parabolic e j (hg.imp hj.trans hj.trans)
end Theory.SpecificGroups.SymplecticFour
namespace Atlas.G2
open LieParabolicSetup

theorem no_linearThree_section_in_parabolic
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (hq : 2 < Nat.card F)
    (f : B →* Model F) [Group.IsSolvable f.ker]
    (hp : f.range ≤ parabolic₁ ∨ f.range ≤ parabolic₂) : False := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases hp with hp | hp
  · have hl : f.range ≤ local₁ := by
      rw [←HigherFieldResiduals.parabolic₁_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict local₁ (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let r := shortSLHom (F := F)
    let : Group.IsSolvable r.ker := by
      rw [show r.ker = radical₁.subgroupOf local₁ from shortSLHom_ker]
      let : Group.IsNilpotent ((radical₁ (F := F)).subgroupOf local₁) :=
        radical₁_isTwoGroup.comap_subtype.isNilpotent
      infer_instance
    exact Matrix.PSL3Two.no_solvable_kernel_rankOne_local e j r
  · have hl : f.range ≤ local₂ := by
      rw [←HigherFieldResiduals.parabolic₂_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ hp
    let j := f.codRestrict local₂ (fun x => hl ⟨x,rfl⟩)
    have hk : j.ker = f.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
    let r := longSLHom (F := F)
    let : Group.IsSolvable r.ker := by
      rw [show r.ker = radical₂.subgroupOf local₂ from longSLHom_ker]
      let : Group.IsNilpotent ((radical₂ (F := F)).subgroupOf local₂) :=
        radical₂_isTwoGroup.comap_subtype.isNilpotent
      infer_instance
    exact Matrix.PSL3Two.no_solvable_kernel_rankOne_local e j r

theorem linearThree_section_sylow_overgroup_eq_top
    (e : (B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)
    (hF : 2 < Nat.card F) (P : Sylow 2 (Model F)) (D : Subgroup (Model F))
    (hPD : (P : Subgroup (Model F)) ≤ D)
    (f : B →* Model F) [Group.IsSolvable f.ker] (hBD : f.range ≤ D) : D = ⊤ := by
  by_contra hD
  obtain ⟨g,hg⟩ := ProperSylowOvergroups.conjugate_le_parabolic P D hPD hD
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hk : j.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  let : Group.IsSolvable j.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable f.ker)
  have hj : j.range ≤ D.map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono hBD
  exact no_linearThree_section_in_parabolic e hF j (hg.imp hj.trans hj.trans)
end Atlas.G2
