module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddG2

/-!
# No projective linear-three outer section in the actual Theorem B catalogue

The prime-field matrices embed SL₃(2) into PSL₃(F) in characteristic two.
The projective scalar kernel does not kill a transvection; simplicity of
SL₃(2) makes this embedding faithful. Pulling back a supplied outer PSL₃(F)
section gives the already excluded outer SL₃(2) section. Full component
central covers and arbitrary kernels of the supplied section are retained.
Source: Aschbacher--Smith 4.4.10--11, printed p.621, applied to 7.3.4, p.699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource

private theorem exists_binary_projective_embedding
    (F : Type*) [Field F] [CharP F 2] :
    ∃ j : BinaryLinearThree.Group →* PSL(3,F), Function.Injective j := by
  let ι : ZMod 2 →+* F := ZMod.castHom (by simp) F
  let m : BinaryLinearThree.Group →* SL(3,F) := Matrix.SpecialLinearGroup.map ι
  let j := (QuotientGroup.mk' (center SL(3,F))).comp m
  let : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hne : j ≠ 1 := by
    intro hz
    let t : BinaryLinearThree.Group := Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) 1
    have ht : m t = Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 3) ≠ 1 by decide) (1 : F) := by
      apply Subtype.ext
      ext i k
      change ι ((Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2)).val i k) = _
      simp [Matrix.SpecialLinearGroup.transvection_coe,Matrix.one_apply,Matrix.single_apply]
    have hj : j t = 1 := DFunLike.congr_fun hz t
    have hc : m t ∈ center SL(3,F) := (QuotientGroup.eq_one_iff (m t)).mp hj
    rw [ht,Matrix.SpecialLinearGroup.transvection_mem_center_iff] at hc
    exact one_ne_zero hc
  have hi : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff j).mp
    rcases (inferInstance : j.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (hne (MonoidHom.ker_eq_top_iff.mp ht)).elim
  exact ⟨j,hi⟩

/-- No full projective linear-three group in characteristic two is an
outer section of a component in the complete Theorem B catalogue. -/
theorem no_theoremB_linear_three_outer_section
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (F : Type*) [Field F] [CharP F 2]
    (U : Subgroup (MulAut.Outer K)) (f : U →* PSL(3,F))
    (hf : Function.Surjective f) : False := by
  obtain ⟨j,hj⟩ := exists_binary_projective_embedding F
  let e := MonoidHom.ofInjective hj
  let P := j.range.comap f
  let q : P →* BinaryLinearThree.Group :=
    e.symm.toMonoidHom.comp (f.subgroupComap j.range)
  have hq : Function.Surjective q := e.symm.surjective.comp
    (f.subgroupComap_surjective_of_surjective j.range hf)
  let a := P.equivMapOfInjective U.subtype U.subtype_injective
  exact (DoubledBinaryOddG2.no_theoremB_outer_section hm)
    ⟨P.map U.subtype,q.comp a.symm.toMonoidHom,hq.comp a.symm.surjective⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
