module

public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Core

/-!
# The short geometric parabolic and the standard G₂ overlap

The first parabolic is the full stabilizer of the null plane spanned by the
first two octonion basis vectors. The long parabolic's scalar, partner, and
SL₂ normal form shows that preserving this plane forces its SL₂ block to be
upper triangular. Thus its intersection with the plane stabilizer is precisely
the Borel. A root-and-torus reduction of a nonzero plane vector then proves
that the root-defined short parabolic is the full geometric stabilizer.
These statements hold over every field, including the binary parameter.

Source: Aschbacher--Smith, F.1.12(I)(3), printed pp. 262--264.
The octonion geometry and long parabolic normal form use the licensed ATLAS
port in the imported modules (LICENSES/ATLAS.txt).
-/

@[expose] public section
namespace Atlas.G2.LieParabolicSetup
open Explicit Atlas.SplitOctonion PairStabilizer
open scoped MatrixGroups
variable {F : Type*} [Field F]
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section

/-- The standard null plane in the split octonions. -/
def shortPlane : Submodule F (Carrier F) where
  carrier := {x | ∀ i : Fin 8, 2 ≤ i.val → x i = 0}
  zero_mem' := by simp
  add_mem' hx hy i hi := by simp [hx i hi, hy i hi]
  smul_mem' a x hx i hi := by simp [hx i hi]

theorem shortPlane_coordinates {x : Carrier F} (hx : x ∈ shortPlane) :
    x = ![x 0,x 1,0,0,0,0,0,0] := by
  funext i
  fin_cases i
  all_goals first | rfl | exact hx _ (by decide)

theorem basis_mem_shortPlane (i : Fin 8) (hi : i.val < 2) :
    basisVector i ∈ shortPlane (F := F) := by
  intro j hj
  have hne : j ≠ i := by intro h; subst j; omega
  simp [basisVector,hne]

/-- The full geometric stabilizer, including preservation by the inverse. -/
def shortPlaneStabilizer : Subgroup (Model F) where
  carrier := {g | (∀ x ∈ shortPlane, g.val x ∈ shortPlane) ∧
    (∀ x ∈ shortPlane, g.val.symm x ∈ shortPlane)}
  one_mem' := ⟨fun _ hx => hx, fun _ hx => hx⟩
  mul_mem' hg hh := ⟨fun x hx => hg.1 _ (hh.1 x hx),
    fun x hx => hh.2 _ (hg.2 x hx)⟩
  inv_mem' hg := ⟨hg.2,hg.1⟩

private theorem le_shortPlaneStabilizer (H : Subgroup (Model F))
    (hH : ∀ g ∈ H, ∀ x ∈ shortPlane, g.val x ∈ shortPlane) : H ≤ shortPlaneStabilizer :=
  fun g hg => ⟨hH g hg, hH g⁻¹ (H.inv_mem hg)⟩

theorem unipotent_le_shortPlaneStabilizer : unipotent (K := F) ≤ shortPlaneStabilizer := by
  apply le_shortPlaneStabilizer
  intro g hg x hx
  rw [unipotent_eq_range] at hg
  obtain ⟨t,rfl⟩ := hg
  rw [shortPlane_coordinates hx]
  intro i hi
  fin_cases i <;>
    simp_all [unipotentProduct,rootA,rootB,rootC,rootD,rootE,rootF,
      rootAEquiv,rootBEquiv,rootCEquiv,rootDEquiv,rootEEquiv,rootFEquiv,
      rootALinear,rootBLinear,rootCLinear,rootDLinear,rootELinear,rootFLinear,
      rootAApply,rootBApply,rootCApply,rootDApply,rootEApply,rootFApply]

theorem torus_le_shortPlaneStabilizer : splitTorus (K := F) ≤ shortPlaneStabilizer := by
  apply le_shortPlaneStabilizer
  rintro g ⟨⟨l,m⟩,rfl⟩ x hx i hi
  change (torusWeights l m i : F) * x i = 0
  rw [hx i hi,mul_zero]

theorem weylS_mem_shortPlaneStabilizer : (weylS : Model F) ∈ shortPlaneStabilizer := by
  have h : ∀ x ∈ shortPlane (F := F), weylS.val x ∈ shortPlane := by
    intro x hx
    rw [shortPlane_coordinates hx]
    intro i hi
    fin_cases i <;> simp_all [weylS,weylSEquiv,weylSLinear,weylSApply]
  exact ⟨h,h⟩

theorem borel_le_shortPlaneStabilizer : borel (K := F) ≤ shortPlaneStabilizer :=
  sup_le unipotent_le_shortPlaneStabilizer torus_le_shortPlaneStabilizer

theorem parabolic₁_le_shortPlaneStabilizer : parabolic₁ (F := F) ≤ shortPlaneStabilizer :=
  sup_le borel_le_shortPlaneStabilizer
    ((Subgroup.closure_le _).mpr (by simpa using weylS_mem_shortPlaneStabilizer (F := F)))

private theorem block_mem_borel_of_lower_zero (M : SL(2,F)) (hM : M.val 1 0 = 0) :
    blockHom M ∈ borel := by
  have hd : M.val 0 0 * M.val 1 1 = 1 := by
    have h := M.prop
    rw [Matrix.det_fin_two] at h
    simpa only [hM,mul_zero,sub_zero] using h
  have ha : M.val 0 0 ≠ 0 := by intro h; simp [h] at hd
  let a : Fˣ := Units.mk0 (M.val 0 0) ha
  have hd' : M.val 1 1 = (a⁻¹ : Fˣ) := by
    change M.val 1 1 = (M.val 0 0)⁻¹
    exact eq_inv_of_mul_eq_one_right hd
  have he : blockHom M = torus 1 a * rootE (M.val 0 1 / (a : F)) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext i
    fin_cases i <;>
      simp [blockHom,blockEquiv,blockLinear,torus,torusEquiv,torusLinear,torusWeights,
        rootE,rootEEquiv,rootELinear,rootEApply,hM,hd',a] <;> field_simp
  rw [he]
  exact borel.mul_mem (Subgroup.mem_sup_right ⟨(1,a),rfl⟩)
    (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))

/-- The long parabolic preserving the standard null plane is exactly the Borel. -/
theorem shortPlaneStabilizer_inf_parabolic₂ :
    shortPlaneStabilizer (F := F) ⊓ parabolic₂ = borel := by
  apply le_antisymm
  · intro g hg
    let p : pointStabilizer (K := F) := ⟨g, (parabolic_eq_pointStabilizer (F := F)).le hg.2⟩
    let n := normalizePoint p
    let r := normalizedPair n
    have htB : torus (lineScalar p) 1 ∈ borel (K := F) :=
      Subgroup.mem_sup_right ⟨(_,1),rfl⟩
    have hcB : chartReducer (partnerOf n).val ∈ borel (K := F) :=
      Subgroup.mem_sup_left (chartReducer_mem_unipotent _)
    have hn : n.val ∈ shortPlaneStabilizer (F := F) :=
      shortPlaneStabilizer.mul_mem
        (shortPlaneStabilizer.inv_mem (borel_le_shortPlaneStabilizer htB)) hg.1
    have hr : r.val ∈ shortPlaneStabilizer (F := F) :=
      shortPlaneStabilizer.mul_mem (borel_le_shortPlaneStabilizer hcB) hn
    have he := congrArg Subtype.val (block_imageSL r)
    change blockHom (imageSL r) = r.val at he
    have hzero : (imageSL r).val 1 0 = 0 := by
      have hx := hr.1 (basisVector 1) (basis_mem_shortPlane 1 (by decide)) 2 (by decide)
      rw [← he] at hx
      simpa [blockHom,blockEquiv,blockLinear,basisVector] using hx
    have hb := block_mem_borel_of_lower_zero (imageSL r) hzero
    rw [he] at hb
    have hh := borel.mul_mem htB (borel.mul_mem (borel.inv_mem hcB) hb)
    change torus (lineScalar p) 1 *
      ((chartReducer (partnerOf n).val)⁻¹ *
        (chartReducer (partnerOf n).val * ((torus (lineScalar p) 1)⁻¹ * g))) ∈ borel at hh
    simpa only [inv_mul_cancel_left, mul_inv_cancel_left] using hh
  · exact le_inf borel_le_shortPlaneStabilizer borel_le_parabolic₂

/-- The whole standard overlap, over every field. -/
theorem parabolics_intersection : parabolic₁ (F := F) ⊓ parabolic₂ = borel := by
  apply le_antisymm
  · exact (inf_le_inf_right _ parabolic₁_le_shortPlaneStabilizer).trans
      shortPlaneStabilizer_inf_parabolic₂.le
  · exact le_inf borel_le_parabolic₁ borel_le_parabolic₂

/-- All products of vectors in the standard plane vanish. -/
theorem shortPlane_mul {x y : Carrier F} (hx : x ∈ shortPlane) (hy : y ∈ shortPlane) :
    Atlas.SplitOctonion.mul x y = 0 := by
  rw [shortPlane_coordinates hx, shortPlane_coordinates hy]
  funext i
  fin_cases i <;> simp [Atlas.SplitOctonion.mul]

private theorem shortPlane_reduction (x : Carrier F) (hx : x ∈ shortPlane) (hne : x ≠ 0) :
    ∃ r ∈ parabolic₁ (F := F), r.val x = basisVector 0 := by
  have ht : ∀ l m : Fˣ, torus l m ∈ parabolic₁ (F := F) :=
    fun l m => borel_le_parabolic₁ (Subgroup.mem_sup_right ⟨(l,m),rfl⟩)
  by_cases hb : x 1 = 0
  · have ha : x 0 ≠ 0 := by
      intro ha
      apply hne
      rw [shortPlane_coordinates hx,ha,hb]
      ext i
      fin_cases i <;> rfl
    let a : Fˣ := Units.mk0 (x 0) ha
    refine ⟨torus a⁻¹ 1,ht _ _,?_⟩
    rw [shortPlane_coordinates hx]
    funext i
    fin_cases i <;> simp [torus,torusEquiv,torusLinear,torusWeights,basisVector,a,hb,ha]
  · let b : Fˣ := Units.mk0 (-(x 1)) (neg_ne_zero.mpr hb)
    refine ⟨torus b⁻¹ 1 * weylS * rootF (x 0 / x 1),?_,?_⟩
    · exact parabolic₁.mul_mem
        (parabolic₁.mul_mem (ht _ _)
          (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))))
        (borel_le_parabolic₁ (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))))
    · rw [shortPlane_coordinates hx]
      funext i
      fin_cases i <;>
        simp [torus,torusEquiv,torusLinear,torusWeights,weylS,weylSEquiv,weylSLinear,weylSApply,
          rootF,rootFEquiv,rootFLinear,rootFApply,basisVector,b,hb]

/-- The root-defined first parabolic is the full standard null-plane stabilizer. -/
theorem parabolic₁_eq_shortPlaneStabilizer : parabolic₁ (F := F) = shortPlaneStabilizer := by
  apply le_antisymm parabolic₁_le_shortPlaneStabilizer
  intro g hg
  have hx := hg.1 (basisVector 0) (basis_mem_shortPlane 0 (by decide))
  have hne : g.val (basisVector 0) ≠ 0 := by
    intro hz
    exact first_basis_ne_zero (g.val.injective (hz.trans (map_zero g.val).symm))
  obtain ⟨r,hr,he⟩ := shortPlane_reduction _ hx hne
  have hp : r*g ∈ parabolic₂ := by
    change r*g ∈ parabolic
    rw [parabolic_eq_pointStabilizer]
    apply (mem_pointStabilizer_iff _).mpr
    exact ⟨1,by simpa using he⟩
  have hs : r*g ∈ shortPlaneStabilizer (F := F) :=
    shortPlaneStabilizer.mul_mem (parabolic₁_le_shortPlaneStabilizer hr) hg
  have hb : r*g ∈ borel (K := F) := shortPlaneStabilizer_inf_parabolic₂.le ⟨hs,hp⟩
  have hh := parabolic₁.mul_mem (parabolic₁.inv_mem hr) (borel_le_parabolic₁ hb)
  simpa only [inv_mul_cancel_left] using hh

end
end Atlas.G2.LieParabolicSetup
