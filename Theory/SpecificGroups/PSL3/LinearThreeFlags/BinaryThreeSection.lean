module
public import Theory.SpecificGroups.SL2.BinaryThreeSection
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups

/-!
# Binary-three sections in the actual linear-three parabolics

A perfect subgroup of either parabolic lies in its vector or covector
stabilizer. The latter has binary SL₂ two-core quotient, so it cannot
receive a perfect group with an SL₃(2) quotient through a two-group kernel.
The coordinate character proof includes the field with two elements.
Full-Sylow overgroup placement then forces any overgroup of such an image
to be all of PSL₃. Both the quotient map and the original image are retained.

Source application: Aschbacher--Smith A.3.12 and 10.2.6,
printed pp.47--48 and 748--749.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

private def pointCharacter : pointParabolicSL F →* F where
  toFun g := g.val.val 0 0
  map_one' := by simp
  map_mul' g h := by
    have hh := (mem_pointParabolicSL_iff F h).mp h.property
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hh.1, hh.2]

private def lineCharacter : lineParabolicSL F →* F where
  toFun g := g.val.val 2 2
  map_one' := by simp
  map_mul' g h := by
    have hg := (mem_lineParabolicSL_iff F g).mp g.property
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2]

private theorem point_residual_le :
    (solvableResidual (pointParabolic F)).map (pointParabolic F).subtype ≤ pointLocal F := by
  have hsl : (solvableResidual (pointParabolicSL F)).map (pointParabolicSL F).subtype ≤
      pointLocalSL F := by
    have h := map_solvableResidual_le (pointCharacter F).toHomUnits
    rw [solvableResidual_eq_bot (G := Fˣ),le_bot_iff,Subgroup.map_eq_bot_iff] at h
    rintro g ⟨x,hx,rfl⟩
    have he := congrArg (fun a : Fˣ => (a : F)) (h hx)
    exact (mem_pointLocalSL_iff F x).mpr ⟨he,(mem_pointParabolicSL_iff F x).mp x.property⟩
  let f := (projection F).subgroupMap (pointParabolicSL F)
  have hm := congrArg
    (fun A : Subgroup ((pointParabolicSL F).map (projection F)) =>
      A.map ((pointParabolicSL F).map (projection F)).subtype)
    (map_solvableResidual_eq f ((projection F).subgroupMap_surjective _))
  rw [Subgroup.map_map] at hm
  have he : ((pointParabolicSL F).map (projection F)).subtype.comp f =
      (projection F).comp (pointParabolicSL F).subtype := rfl
  rw [he, ←Subgroup.map_map] at hm
  exact hm.symm.le.trans (map_mono (f := projection F) hsl)

private theorem line_residual_le :
    (solvableResidual (lineParabolic F)).map (lineParabolic F).subtype ≤ lineLocal F := by
  have hsl : (solvableResidual (lineParabolicSL F)).map (lineParabolicSL F).subtype ≤
      lineLocalSL F := by
    have h := map_solvableResidual_le (lineCharacter F).toHomUnits
    rw [solvableResidual_eq_bot (G := Fˣ),le_bot_iff,Subgroup.map_eq_bot_iff] at h
    rintro g ⟨x,hx,rfl⟩
    have he := congrArg (fun a : Fˣ => (a : F)) (h hx)
    have hp := (mem_lineParabolicSL_iff F x).mp x.property
    exact (mem_lineLocalSL_iff F x).mpr ⟨hp.1,hp.2,he⟩
  let f := (projection F).subgroupMap (lineParabolicSL F)
  have hm := congrArg
    (fun A : Subgroup ((lineParabolicSL F).map (projection F)) =>
      A.map ((lineParabolicSL F).map (projection F)).subtype)
    (map_solvableResidual_eq f ((projection F).subgroupMap_surjective _))
  rw [Subgroup.map_map] at hm
  have he : ((lineParabolicSL F).map (projection F)).subtype.comp f =
      (projection F).comp (lineParabolicSL F).subtype := rfl
  rw [he, ←Subgroup.map_map] at hm
  exact hm.symm.le.trans (map_mono (f := projection F) hsl)

variable [CharP F 2]

/-- Neither actual parabolic admits this binary-three section. -/
theorem no_binary_three_quotient_in_parabolic
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (π : A →* SL(3,ZMod 2)) (hπ : Function.Surjective π)
    (f : A →* PSL(3,F)) (hf : IsPGroup 2 f.ker)
    (hP : f.range ≤ pointParabolic F ∨ f.range ≤ lineParabolic F) : False := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases hP with hP | hP
  · have hl : f.range ≤ pointLocal F :=
      (le_map_solvableResidual_of_isPerfect _ _ hP).trans (point_residual_le F)
    let g := f.codRestrict (pointLocal F) (fun a => hl ⟨a,rfl⟩)
    have hg : IsPGroup 2 g.ker := by
      have he : g.ker = f.ker := MonoidHom.ker_codRestrict _ _ _
      rwa [he]
    exact SpecialLinearGroup.no_binary_three_quotient_of_binary_core_quotient
      π hπ g hg (pointLocalCoreQuotientEquiv F)
  · have hl : f.range ≤ lineLocal F :=
      (le_map_solvableResidual_of_isPerfect _ _ hP).trans (line_residual_le F)
    let g := f.codRestrict (lineLocal F) (fun a => hl ⟨a,rfl⟩)
    have hg : IsPGroup 2 g.ker := by
      have he : g.ker = f.ker := MonoidHom.ker_codRestrict _ _ _
      rwa [he]
    exact SpecialLinearGroup.no_binary_three_quotient_of_binary_core_quotient
      π hπ g hg (lineLocalCoreQuotientEquiv F)

/-- A full Sylow and the original binary-three section generate the whole carrier. -/
theorem sylow_overgroup_eq_top_of_binary_three_quotient
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (π : A →* SL(3,ZMod 2)) (hπ : Function.Surjective π)
    (f : A →* PSL(3,F)) (hf : IsPGroup 2 f.ker)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 PSL(3,F)) (P : Subgroup PSL(3,F))
    (hSP : (S : Subgroup PSL(3,F)) ≤ P) (hfP : f.range ≤ P) : P = ⊤ := by
  by_contra hne
  obtain ⟨g,hg⟩ := UnipotentOvergroups.proper_sylow_overgroup_parabolic_cover F hn hF S P hSP hne
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj : IsPGroup 2 j.ker := by
    have he : j.ker = f.ker := by
      ext a
      exact (MulAut.conj g).map_eq_one_iff
    rwa [he]
  have hjP : j.range ≤ P.map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono hfP
  exact no_binary_three_quotient_in_parabolic F π hπ j hj (hg.imp hjP.trans hjP.trans)

end Matrix.PSL3.LinearThree
