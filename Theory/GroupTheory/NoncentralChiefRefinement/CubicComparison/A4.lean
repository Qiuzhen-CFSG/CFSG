module
public import Theory.Alternating.theorem_5_2_1_2
public import Theory.GroupAction.NoncentralTwoChiefLength.Native
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex
set_option linter.style.haveILetI false
public section
open Subgroup
open scoped Pointwise
namespace GLS3.Chapter5
noncomputable section
abbrev U := alternatingFourKlein
abbrev C := Subgroup.zpowers alternatingFourThreeCycle

instance U_normal : U.Normal := inferInstance

theorem u_length_one : conjugationCubicLength C U = 1 := by
  have hnorm : C ≤ normalizer (U : Set (alternatingGroup (Fin 4))) := le_normalizer_of_normal
  letI := conjMulDistribMulActionOfLeNormalizer C U hnorm
  have hfix : FixedPoints.subgroup C U = ⊥ := by
    ext x
    constructor
    · intro hx
      have hx0 := hx (⟨alternatingFourThreeCycle, Subgroup.mem_zpowers _⟩ : C)
      have hx0' : alternatingFourThreeCycle * (x : alternatingGroup (Fin 4)) *
          alternatingFourThreeCycle⁻¹ = (x : alternatingGroup (Fin 4)) := by
        exact congrArg Subtype.val hx0
      have : (x : alternatingGroup (Fin 4)) = 1 := by
        exact (alternatingFourThreeCycle_conj_fixed_iff x).mp hx0'
      exact (show x = 1 from Subtype.ext this)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst x
      intro a
      simp
  rw [conjugationCubicLength_eq C U hnorm]
  unfold FixedPoints.cubicLength
  rw [hfix]
  simp [Subgroup.index_bot, alternatingFourKlein_card]
  decide
end
end GLS3.Chapter5
