module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.FieldFour
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# A marked full SL₃(4) cover has no exceptional even kernel

Restrict the original Sylow and elementary complement to the full lifted
plane parabolic. Injectivity of projective projection on the root local
preserves disjointness from the kernel, and the actual radical image
becomes the affine translations. The proved invariant-complement theorem
then forces the projective covering kernel to be odd. The full SL₃ cover
is retained; projective projection is only the intermediate model map.

Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774,
first three paragraphs. The exceptional model calculation uses I.2.2(3b).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
namespace FieldFour
open Matrix.PSL3Four Matrix.PSL3Four.ElementaryParabolic
open Matrix.PSL3.LinearThree
open scoped MatrixGroups
variable {E : Type*} [Group E] [Finite E]

/-- A full SL₃(4) covering with the literal Sylow-invariant plane-radical
complement has odd projective kernel. -/
theorem full_cover_projective_kernel_odd
    (f : PerfectCentralCovering.Cover E SL(3,Matrix.PSL3Four.F))
    (R : Sylow 2 E)
    (hR : (R : Subgroup E).map f.toMonoidHom ≤ lineParabolicSL Matrix.PSL3Four.F)
    (C : Subgroup E) [IsMulCommutative C]
    (hd : Disjoint f.toMonoidHom.ker C)
    (hC : C.map f.toMonoidHom = (lineRadicalSL Matrix.PSL3Four.F).map
      (lineLocalSL Matrix.PSL3Four.F).subtype)
    (hn : (R : Subgroup E) ≤ normalizer (C : Set E)) :
    ¬ 2 ∣ Nat.card ((Matrix.PSL3.projection Matrix.PSL3Four.F).comp f.toMonoidHom).ker := by
  let F := Matrix.PSL3Four.F
  let g : E →* Matrix.PSL3Four.PSL := (Matrix.PSL3.projection F).comp f.toMonoidHom
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective _).comp f.surjective
  have hgc : g.ker ≤ center E := by
    dsimp only [g]
    rw [←MonoidHom.comap_ker,Matrix.PSL3.projection_ker]
    exact f.comap_center.le
  have hCL (x : E) (hx : x ∈ C) : f.toMonoidHom x ∈ lineLocalSL F := by
    obtain ⟨y,hy,he⟩ := hC.le (mem_map_of_mem _ hx)
    exact he ▸ y.property
  have hCP : C ≤ liftedParabolic g false := by
    intro x hx
    exact mem_map_of_mem (Matrix.PSL3.projection F) (lineLocalSL_le F (hCL x hx))
  have hRP : (R : Subgroup E) ≤ liftedParabolic g false := by
    intro x hx
    exact mem_map_of_mem (Matrix.PSL3.projection F) (hR (mem_map_of_mem _ hx))
  have hdg : Disjoint g.ker C := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hcx
    have he : (⟨f.toMonoidHom x,hCL x hcx⟩ : lineLocalSL F) = 1 := by
      apply (lineLocalProjectEquiv F).injective
      apply Subtype.ext
      exact hx
    have hk : x ∈ f.toMonoidHom.ker := congrArg Subtype.val he
    exact Subgroup.disjoint_def.mp hd hk hcx
  let P := liftedParabolic g false
  let A := C.subgroupOf P
  let e := subgroupOfEquivOfLe hCP
  let : IsMulCommutative A := ⟨⟨fun x y => e.injective (by
    rw [map_mul,map_mul,mul_comm])⟩⟩
  have ha (x : P) (hx : (x : E) ∈ C) :
      parabolicAffine g false x = lineLocalAffineEquiv F ⟨f.toMonoidHom x,hCL x hx⟩ := by
    change lineLocalEquivAffine F ⟨g x,_⟩ = _
    change lineLocalAffineEquiv F ((lineLocalProjectEquiv F).symm
      (lineLocalProjectEquiv F ⟨f.toMonoidHom x,hCL x hx⟩)) = _
    rw [MulEquiv.symm_apply_apply]
  have him : A.map (parabolicAffine g false) = Matrix.SL2.translations F := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [ha x hx]
      have hfx := hC.le (mem_map_of_mem f.toMonoidHom hx)
      obtain ⟨y,hy,he⟩ := hfx
      have he' : (⟨f.toMonoidHom x,hCL x hx⟩ : lineLocalSL F) = y := Subtype.ext he.symm
      rw [he']
      exact hy
    · intro y hy
      let z := (lineLocalAffineEquiv F).symm y
      have hz : z ∈ lineRadicalSL F := by
        change SemidirectProduct.rightHom (lineLocalAffineEquiv F z) = 1
        rw [MulEquiv.apply_symm_apply]
        exact hy
      obtain ⟨x,hx,hfx⟩ := hC.ge (mem_map_of_mem (lineLocalSL F).subtype hz)
      let xp : P := ⟨x,hCP hx⟩
      refine ⟨xp,hx,?_⟩
      rw [ha xp hx]
      have he : (⟨f.toMonoidHom xp,hCL xp hx⟩ : lineLocalSL F) = z := Subtype.ext hfx
      rw [he,MulEquiv.apply_symm_apply]
  have hd' : Disjoint (parabolicAffine g false).ker A := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hy
    rw [parabolicAffine_ker] at hx
    exact Subtype.ext (Subgroup.disjoint_def.mp hdg hx hy)
  have hn' : (R.subtype hRP : Subgroup P) ≤ normalizer (A : Set P) := by
    apply le_normalizer_iff.mpr
    intro r hr x hx
    exact le_normalizer_iff.mp hn (r : E) hr (x : E) hx
  let := f.isPerfect
  exact parabolic_kernel_odd_of_abelian_image g hg hgc false (R.subtype hRP) A hd' him hn'

end FieldFour
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
