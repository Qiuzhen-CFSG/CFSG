module

public import Theory.AlgebraicGroup.Bor1.BlockConjugationDifferential
public import Theory.AlgebraicGroup.Bor1.ChevalleyExteriorRepresentationDifferential
public import Theory.AlgebraicGroup.Bor1.ChevalleyWeightExactKernel
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialKernel
public import Theory.AlgebraicGroup.Bor1.WeightLineDifferential

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A regular finite-dimensional representation whose point kernel and
identity differential kernel are both exactly a prescribed closed subgroup. -/
public structure ExactKernelDifferentialRationalRepresentation
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) where
  V : Type u
  [addCommGroup : AddCommGroup V]
  [module : Module k V]
  [finiteDimensional : FiniteDimensional k V]
  representation : RationalRepresentation G V
  basis : Module.Basis (Fin (Module.finrank k V)) k V
  morphism : AlgebraicGroup.Morphism G (glVarietyOf k V)
  pointAction : ∀ g,
    glPointEquivOf k V basis (morphism.onPoints g) = representation.action g
  pointKernel : representation.action.ker = H.toSubgroup
  differentialKernel :
    LinearMap.ker (rationalRepresentationDifferential
      representation basis morphism) =
        LinearMap.range (identityTangentMorphismLinearMap H.inclusion)

set_option linter.style.haveILetI false in
/-- Bor1's common-weight block-conjugation construction gives every normal
closed subgroup a rational representation with exact point and differential
kernels. -/
public theorem ClosedSubgroup.chevalleyWeightBlockExactDifferentialKernel_nonempty
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    Nonempty (ExactKernelDifferentialRationalRepresentation H) := by
  let _ : H.toSubgroup.Normal := hN
  letI commonWeightAddCommGroup : AddCommGroup (chevalleyCommonWeightSpan H) :=
    Submodule.addCommGroup (chevalleyCommonWeightSpan H)
  letI commonWeightModule : Module k (chevalleyCommonWeightSpan H) :=
    Submodule.module (chevalleyCommonWeightSpan H)
  letI commonWeightFiniteDimensional :
      FiniteDimensional k (chevalleyCommonWeightSpan H) := inferInstance
  obtain ⟨τ, hτ, hτrat⟩ :=
    ClosedSubgroup.exists_chevalleyCommonWeightRestriction H hN
  obtain ⟨b, f, hf⟩ := hτrat
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
                H.rightTranslateVanishingSpan) := hτ
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
        E ((perm g : Equiv _ _) i) :=
    Representation.commonWeightBlock_map_of_restriction
      σ H.toSubgroup τ.action hτpoint
  let W : Submodule k (Module.End k (chevalleyCommonWeightSpan H)) :=
    blockDiagonalEnd (k := k) (V := chevalleyCommonWeightSpan H)
      (ι := Representation.commonWeightIndex σ H.toSubgroup) E
  letI blockAddCommGroup : AddCommGroup W := Submodule.addCommGroup W
  letI blockModule : Module k W := Submodule.module W
  letI blockFiniteDimensional : FiniteDimensional k W := inferInstance
  let β : RationalRepresentation G W :=
    blockDiagonalEndConjRationalRepresentation E τ perm hE
  have hβrat : IsRationalRepresentation β :=
    blockDiagonalEndConjRationalRepresentation_isRational
      E τ ⟨b, f, hf⟩ perm hE
  obtain ⟨c, F, hF⟩ := hβrat
  have hβker : β.action.ker = H.toSubgroup := by
    change (blockDiagonalEnd_conjRepresentation E τ.action perm hE).ker =
      H.toSubgroup
    refine Representation.commonWeightBlock_conjRepresentation_ker_eq_of_vectorLineStabilizer
      σ H.toSubgroup H.rightTranslateVanishingPluckerVector
      H.rightTranslateVanishingPluckerVector_ne_zero ?_ τ.action hτpoint
    intro g
    exact H.chevalleyPluckerLine_stabilizer_iff g
  have hdiffker :
      LinearMap.ker (rationalRepresentationDifferential β c F) =
        LinearMap.range (identityTangentMorphismLinearMap H.inclusion) := by
    apply le_antisymm
    · intro D hD
      rw [LinearMap.mem_ker] at hD
      have hcentral : ∀ u : W,
          Commute (rationalRepresentationDifferential τ b f D) u.1 := by
        exact blockDiagonalEnd_rationalRepresentationDifferential_eq_zero_imp_centralizes
          E τ perm hE b f hf c F hF D hD
      obtain ⟨e, q, hq⟩ :=
        H.rightTranslateVanishingExteriorRationalRepresentation_isRational
      have hNLine : ∀ n : H.toSubgroup,
          (ρ.action n.1 : Module.End k
            (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
              H.rightTranslateVanishingSpan))
              H.rightTranslateVanishingPluckerVector ∈
            k ∙ H.rightTranslateVanishingPluckerVector := by
        intro n
        exact (H.chevalleyPluckerLine_stabilizer_iff n.1).mpr n.2
      have hline :=
        RationalRepresentation.differential_mem_vectorLine_of_commonWeightBlock_centralizer
          ρ H.toSubgroup H.rightTranslateVanishingPluckerVector
          H.rightTranslateVanishingPluckerVector_ne_zero hNLine
          τ hτ b f hf e q hq D hcentral
      rw [ClosedSubgroup.rationalRepresentationDifferential_plucker_eq_chevalleyExterior
        H
        e q hq D] at hline
      exact
        ClosedSubgroup.identityTangent_mem_range_of_chevalleyExteriorWedgeDifferential_line
          H D hline
    · intro D hD
      obtain ⟨d, rfl⟩ := hD
      rw [LinearMap.mem_ker]
      exact rationalRepresentationDifferential_comp_inclusion_eq_zero_of_kernel_le
        H β c F hF (by rw [hβker]) d
  exact ⟨{
    V := W
    representation := β
    basis := c
    morphism := F
    pointAction := hF
    pointKernel := hβker
    differentialKernel := hdiffker }⟩

end Theory.AlgebraicGroup.Bor1
