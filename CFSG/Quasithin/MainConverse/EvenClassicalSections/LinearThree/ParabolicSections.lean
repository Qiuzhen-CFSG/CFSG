module

public import CFSG.Quasithin.MainConverse.RankOneSections.Linear
public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.Basic
public import Theory.SpecificGroups.PSL3.LinearThreeLocalAffine

/-!
# Simple sections of the full degree-three parabolics

The lower two-by-two block maps the full point stabilizer in SL₃ to GL₂.
Its kernel consists of the abelian first-row shears. The determinant kernel
in GL₂ is SL₂, whose central quotient is PSL₂; Dickson therefore identifies
every simple section. Projection gives the full projective point parabolic,
and inverse transpose transfers the result to the line parabolic.

This proves the parabolic case of the proper-subgroup calculation, over any
finite field. It does not assert an exhaustion of proper subgroups of PSL₃.
Source: GLS3, Theorem 6.5.3(a), `refs/KGroup/GLS3/chapter6.tex`; the condition
K in Aschbacher–Smith, Main Hypothesis 0.1.1, printed pp.4 and 482.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open CFSG.KnownSimple Matrix Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups

private theorem isKGroup_of_solvable_kernel {G H : Type*} [Group G] [Group H]
    (f : G →* H) [Group.IsSolvable f.ker]
    (hH : IsKGroup IsConstructedCarrier H) : IsKGroup IsConstructedCarrier G := by
  apply IsKGroup.of_normal_quotient f.ker (solvable_isKGroup_constructed _)
  let e := QuotientGroup.quotientKerEquivRange f
  exact SymmetricEight.isKGroup_constructed_of_injective
    (hH.subgroup f.range) e.toMonoidHom e.injective

variable (F : Type) [Field F] [Finite F]

/-- The central extension SL₂ has the same nonabelian simple sections as PSL₂. -/
public theorem sl2_isKGroup_constructed : IsKGroup IsConstructedCarrier SL(2, F) := by
  let : Group.IsSolvable (Subgroup.center SL(2, F)) :=
    Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  apply IsKGroup.of_normal_quotient (Subgroup.center SL(2, F))
    (solvable_isKGroup_constructed _)
  exact psl2_isKGroup_constructed
    ⟨F, inferInstance, inferInstance, rfl, ⟨MulEquiv.refl _⟩⟩

private def determinantKernelToSL :
    (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker →* SL(2, F) where
  toFun g := ⟨g.val.val, by
    have h := congrArg Units.val g.property
    simpa using h⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The determinant quotient of GL₂ is abelian, so Dickson also handles GL₂. -/
public theorem gl2_isKGroup_constructed :
    IsKGroup IsConstructedCarrier (GL (Fin 2) F) := by
  let d : GL (Fin 2) F →* Fˣ := GeneralLinearGroup.det
  have hker : IsKGroup IsConstructedCarrier d.ker :=
    (sl2_isKGroup_constructed F).of_injective (determinantKernelToSL F) (by
      intro a b h
      apply Subtype.ext
      apply Units.ext
      exact congrArg Subtype.val h)
  let e := QuotientGroup.quotientKerEquivRange d
  let : Group.IsSolvable (GL (Fin 2) F ⧸ d.ker) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact IsKGroup.of_normal_quotient d.ker hker (solvable_isKGroup_constructed _)

private def pointBlockMatrix : pointParabolicSL F →* Matrix (Fin 2) (Fin 2) F where
  toFun g := g.val.val.submatrix Fin.succ Fin.succ
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' g h := by
    have hg := (mem_pointParabolicSL_iff F g.val).mp g.property
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three,
        Fin.sum_univ_two, submatrix, hg.1, hg.2]

private def pointBlock : pointParabolicSL F →* GL (Fin 2) F :=
  (pointBlockMatrix F).toHomUnits

private theorem pointBlock_kernel_entries (g : (pointBlock F).ker) :
    g.val.val.val 0 0 = 1 ∧ g.val.val.val 1 0 = 0 ∧ g.val.val.val 2 0 = 0 ∧
      g.val.val.val 1 1 = 1 ∧ g.val.val.val 1 2 = 0 ∧
      g.val.val.val 2 1 = 0 ∧ g.val.val.val 2 2 = 1 := by
  have hp := (mem_pointParabolicSL_iff F g.val.val).mp g.val.property
  have h := congrArg Units.val g.property
  change g.val.val.val.submatrix Fin.succ Fin.succ = 1 at h
  have h11 := congrArg (fun a : Matrix (Fin 2) (Fin 2) F => a 0 0) h
  have h12 := congrArg (fun a : Matrix (Fin 2) (Fin 2) F => a 0 1) h
  have h21 := congrArg (fun a : Matrix (Fin 2) (Fin 2) F => a 1 0) h
  have h22 := congrArg (fun a : Matrix (Fin 2) (Fin 2) F => a 1 1) h
  change g.val.val.val 1 1 = 1 at h11
  change g.val.val.val 1 2 = 0 at h12
  change g.val.val.val 2 1 = 0 at h21
  change g.val.val.val 2 2 = 1 at h22
  refine ⟨?_, hp.1, hp.2, h11, h12, h21, h22⟩
  have hd := g.val.val.property
  rw [det_fin_three, hp.1, hp.2, h11, h12, h21, h22] at hd
  simpa only [mul_one, mul_zero, sub_zero, add_zero] using hd

private instance pointBlock_kernel_solvable : Group.IsSolvable (pointBlock F).ker := by
  apply Group.isSolvable_of_comm
  intro g h
  obtain ⟨g00, g10, g20, g11, g12, g21, g22⟩ := pointBlock_kernel_entries F g
  obtain ⟨h00, h10, h20, h11, h12, h21, h22⟩ := pointBlock_kernel_entries F h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three,
      g00, g10, g20, g11, g12, g21, g22, h00, h10, h20, h11, h12, h21, h22,
      add_comm]

/-- All simple sections of the full linear point stabilizer are constructed. -/
public theorem pointParabolicSL_isKGroup_constructed :
    IsKGroup IsConstructedCarrier (pointParabolicSL F) :=
  isKGroup_of_solvable_kernel (pointBlock F) (gl2_isKGroup_constructed F)

private def lineToPointSL : lineParabolicSL F →* pointParabolicSL F :=
  ((flagDuality F).toMonoidHom.comp (lineParabolicSL F).subtype).codRestrict
    (pointParabolicSL F) (by
      intro g
      have hg := (mem_lineParabolicSL_iff F _).mp
        ((lineParabolicSL F).inv_mem g.property)
      rw [mem_pointParabolicSL_iff]
      exact ⟨hg.2, hg.1⟩)

/-- Duality gives the full linear line stabilizer, including its torus. -/
public theorem lineParabolicSL_isKGroup_constructed :
    IsKGroup IsConstructedCarrier (lineParabolicSL F) :=
  (pointParabolicSL_isKGroup_constructed F).of_injective (lineToPointSL F) (by
    intro a b h
    exact Subtype.ext ((flagDuality F).injective (congrArg Subtype.val h)))

/-- Projection preserves all simple sections of the full point parabolic. -/
public theorem pointParabolic_isKGroup_constructed :
    IsKGroup IsConstructedCarrier (pointParabolic F) :=
  (pointParabolicSL_isKGroup_constructed F).of_surjective
    ((projection F).subgroupMap (pointParabolicSL F))
    ((projection F).subgroupMap_surjective (pointParabolicSL F))

/-- Projection preserves all simple sections of the full line parabolic. -/
public theorem lineParabolic_isKGroup_constructed :
    IsKGroup IsConstructedCarrier (lineParabolic F) :=
  (lineParabolicSL_isKGroup_constructed F).of_surjective
    ((projection F).subgroupMap (lineParabolicSL F))
    ((projection F).subgroupMap_surjective (lineParabolicSL F))

/-- This includes sections whose simple target inhabits a different universe. -/
public theorem parabolic_simple_section_constructed (point : Bool)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (U : Subgroup ↥(if point then pointParabolic F else lineParabolic F :
      Subgroup PSL(3, F)))
    (f : U →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  apply SymmetricEight.constructed_section_of_isKGroup _ U f hf
  cases point
  · exact lineParabolic_isKGroup_constructed F
  · exact pointParabolic_isKGroup_constructed F

end CFSG.Quasithin.MainConverse.LinearThreeSections
