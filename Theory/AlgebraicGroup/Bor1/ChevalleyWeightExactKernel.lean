module

public import Theory.AlgebraicGroup.Bor1.ChevalleyWeightBlocks
public import Theory.AlgebraicGroup.Bor1.ConjugationRational
public import Theory.AlgebraicGroup.Bor1.ExactKernelRationalRepresentation

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false in
/-- Every normal closed subgroup is the point kernel of the rational
block-conjugation representation obtained from its Chevalley weight spaces. -/
public theorem ClosedSubgroup.chevalleyWeightBlockExactKernel_nonempty
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    Nonempty (ExactKernelRationalRepresentation (k := k) H.toSubgroup) := by
  let _ : H.toSubgroup.Normal := hN
  letI commonWeightAddCommGroup :
      AddCommGroup (chevalleyCommonWeightSpan H) :=
    Submodule.addCommGroup (chevalleyCommonWeightSpan H)
  letI commonWeightModule : Module k (chevalleyCommonWeightSpan H) :=
    Submodule.module (chevalleyCommonWeightSpan H)
  letI commonWeightFiniteDimensional :
      FiniteDimensional k (chevalleyCommonWeightSpan H) :=
    inferInstance
  obtain ⟨τ, hτ, hτrat⟩ :=
    Theory.AlgebraicGroup.Bor1.ClosedSubgroup.exists_chevalleyCommonWeightRestriction H hN
  let ρ := H.rightTranslateVanishingExteriorRationalRepresentation
  let σ := chevalleyExteriorUnderlyingRepresentation H
  have hτpoint : ∀ g x,
      (((τ.action g : Module.End k (chevalleyCommonWeightSpan H)) x :
          chevalleyCommonWeightSpan H) :
          ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan) =
        (ρ.action g : Module.End k
          (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan)) (x :
              ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
                H.rightTranslateVanishingSpan) := by
    exact hτ
  let E : Representation.commonWeightIndex σ H.toSubgroup →
      Submodule k (chevalleyCommonWeightSpan H) :=
    Representation.commonWeightBlock σ H.toSubgroup
  let perm : Variety.Point G →*
      Equiv.Perm (Representation.commonWeightIndex σ H.toSubgroup) :=
    Representation.normalCommonWeightPermutation σ H.toSubgroup
  have hE : ∀ g i, Submodule.map
      ((τ.action g : LinearMap.GeneralLinearGroup k
        (chevalleyCommonWeightSpan H)) : Module.End k
          (chevalleyCommonWeightSpan H)) (E i) =
        E ((perm g : Equiv _ _) i) := by
    exact Representation.commonWeightBlock_map_of_restriction
      σ H.toSubgroup τ.action hτpoint
  let W : Submodule k (Module.End k (chevalleyCommonWeightSpan H)) :=
    blockDiagonalEnd (k := k) (V := chevalleyCommonWeightSpan H)
      (ι := Representation.commonWeightIndex σ H.toSubgroup) E
  letI blockAddCommGroup : AddCommGroup W :=
    Submodule.addCommGroup (R := k)
      (M := Module.End k (chevalleyCommonWeightSpan H)) W
  letI blockModule : Module k W :=
    Submodule.module (R := k)
      (M := Module.End k (chevalleyCommonWeightSpan H)) W
  letI blockFiniteDimensional : FiniteDimensional k W := inferInstance
  let β : RationalRepresentation G W :=
    blockDiagonalEndConjRationalRepresentation E τ perm hE
  have hβrat : IsRationalRepresentation β :=
    blockDiagonalEndConjRationalRepresentation_isRational
      E τ hτrat perm hE
  have hβker : β.action.ker = H.toSubgroup := by
    change (blockDiagonalEnd_conjRepresentation E τ.action perm hE).ker =
      H.toSubgroup
    refine Representation.commonWeightBlock_conjRepresentation_ker_eq_of_vectorLineStabilizer
      σ H.toSubgroup H.rightTranslateVanishingPluckerVector
      H.rightTranslateVanishingPluckerVector_ne_zero ?_ τ.action hτpoint
    intro g
    change
      ((H.rightTranslateVanishingExteriorGeneralLinear g :
        LinearMap.GeneralLinearGroup k
          (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan)) : Module.End k
              (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
                H.rightTranslateVanishingSpan))
          H.rightTranslateVanishingPluckerVector ∈
        k ∙ H.rightTranslateVanishingPluckerVector ↔ g ∈ H.toSubgroup
    exact H.chevalleyPluckerLine_stabilizer_iff g
  exact ⟨{
    V := W
    representation := β
    isRational := hβrat
    pointKernel := hβker }⟩

end Theory.AlgebraicGroup.Bor1
