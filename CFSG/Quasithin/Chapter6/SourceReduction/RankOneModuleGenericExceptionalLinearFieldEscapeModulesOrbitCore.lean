module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesConstituent
public import Theory.Representation.BinaryOffender.HomogeneousOrbitKernel
public import Theory.Quasithin.NormalTwoQuotient

/-!
# The residual orbit's faithful quotient and generalized Fitting subgroup

Every homogeneous seed already constructed on the literal span action has
the same structural conclusion: the central orbit quotient has kernel O₂
of the residual--Sylow join. Its faithful actor has generalized Fitting
subgroup the projected residual, identified with PSL₃(4) by the original
projection. SQTK follows through this two-core quotient from the original
residual and the ambient K-group hypothesis.

This discharges structural premises for the D.3/B.4 constituent argument;
it does not assert the missing orbit collapse or middle-layer fixedness.
Source: Aschbacher--Smith D.3.4 and 5.1.23, printed pp.194,645--646,
`refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
open ChapterG.Section02
universe u v
variable {X : Type u} [Group X] [Finite X]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The exact kernel and F* calculation for any selected homogeneous seed. -/
theorem residual_orbit_structure
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) [K.Normal]
    (hm : ClassicalGroup.IsPSL K 3 4) (hP : IsPGroup 2 P)
    {I : Submodule (ZMod 2) W}
    (hI : IsIrrPlusWith ρ K P I) :
    let σ := orbitSectionRepresentation ρ hI
    σ.ker = pCore 2 (K ⊔ P : Subgroup X) ∧
      generalizedFitting (KernelQuotient.Actor σ) =
        (K.subgroupOf (K ⊔ P)).map (KernelQuotient.projection σ) ∧
      ClassicalGroup.IsPSL ((K.subgroupOf (K ⊔ P)).map
        (KernelQuotient.projection σ)) 3 4 := by
  obtain ⟨hqs,hz,_⟩ := ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm
  let := hqs
  exact ⟨orbitSection_kernel_eq_twoCore ρ hz hP hI,
    orbitSection_faithful_generalizedFitting ρ hz hP hI,
    hm.of_mulEquiv (orbitSectionComponentEquiv ρ hz hI).symm⟩

/-- SQTK is transported through this specific two-core kernel, without
assuming arbitrary quotients preserve the odd-prime rank bound. -/
theorem residual_orbit_sqtk
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) [K.Normal]
    (hm : ClassicalGroup.IsPSL K 3 4) (hP : IsPGroup 2 P)
    (κ : GroupClass.{u}) (hsq : IsSQTK κ K)
    (hkg : IsKGroup κ X)
    {I : Submodule (ZMod 2) W}
    (hI : IsIrrPlusWith ρ K P I) :
    IsSQTK κ
      (KernelQuotient.Actor (orbitSectionRepresentation ρ hI)) := by
  let J := K ⊔ P
  let K₀ := K.subgroupOf J
  let eK : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  have hgen : K₀ ⊔ P.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ J from le_sup_left)
      (show P ≤ J from le_sup_right)]
    exact subgroupOf_self _
  have hquot : IsPGroup 2 (J ⧸ K₀) :=
    quotient_isPGroup_of_sup_eq_top (P.subgroupOf J) K₀ hP.comap_subtype
      ((sup_comm _ _).trans hgen)
  have hsqJ : IsSQTK κ J := by
    refine ⟨?_,hkg.subgroup J⟩
    have hsqK₀ := (IsSQTK.equiv eK).mpr hsq
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_le_of_normal_two_quotient K₀ hquot p ho).trans
      (hsqK₀.stronglyQuasithin p hp ho)
  let σ := orbitSectionRepresentation ρ hI
  have hk : (actionHom σ).ker = pCore 2 J :=
    (actionHom_ker_eq σ).trans (residual_orbit_structure ρ K P hm hP hI).1
  have hk2 : IsPGroup 2 (actionHom σ).ker := by
    rw [hk]
    exact pCore_isPGroup
  refine ⟨?_,hsqJ.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ hk2).trans
    (hsqJ.stronglyQuasithin p hp ho)

/-- Structural properties of each specified seed and its literal central quotient. -/
@[expose] def ResidualOrbitStructure (κ : GroupClass.{u})
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) : Prop :=
  ∀ (I : Submodule (ZMod 2) W) (hI : IsIrrPlusWith ρ K P I),
    let σ := orbitSectionRepresentation ρ hI
    σ.ker = pCore 2 (K ⊔ P : Subgroup X) ∧
      generalizedFitting (KernelQuotient.Actor σ) =
        (K.subgroupOf (K ⊔ P)).map (KernelQuotient.projection σ) ∧
      ClassicalGroup.IsPSL ((K.subgroupOf (K ⊔ P)).map
        (KernelQuotient.projection σ)) 3 4 ∧
      IsSQTK κ (KernelQuotient.Actor σ)

/-- The existing orbit witness with its exact kernel and faithful actor. -/
@[expose] def HasResidualOrbitFittingSection (κ : GroupClass.{u})
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) : Prop :=
  ∃ (I : Submodule (ZMod 2) W) (hI : IsIrrPlusWith ρ K P I),
    let σ := orbitSectionRepresentation ρ hI
    subspaceCommutator ρ (orbitSpan ρ P I) K = orbitSpan ρ P I ∧
      Function.Injective (σ.comp (inclusion (show K ≤ K ⊔ P from le_sup_left))) ∧
      σ.ker = pCore 2 (K ⊔ P : Subgroup X) ∧
      generalizedFitting (KernelQuotient.Actor σ) =
        (K.subgroupOf (K ⊔ P)).map (KernelQuotient.projection σ) ∧
      ClassicalGroup.IsPSL ((K.subgroupOf (K ⊔ P)).map
        (KernelQuotient.projection σ)) 3 4 ∧
      IsSQTK κ (KernelQuotient.Actor σ)

/-- Package the proved conclusions before specializing the nested span action. -/
theorem residual_orbit_structure_all
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) [K.Normal]
    (hm : ClassicalGroup.IsPSL K 3 4) (hP : IsPGroup 2 P)
    (κ : GroupClass.{u}) (hsq : IsSQTK κ K) (hkg : IsKGroup κ X) :
    ResidualOrbitStructure κ ρ K P := by
  intro I hI
  obtain ⟨hk,hf,hm'⟩ := residual_orbit_structure ρ K P hm hP hI
  exact ⟨hk,hf,hm',residual_orbit_sqtk ρ K P hm hP κ hsq hkg hI⟩

omit [Finite X] [FiniteDimensional (ZMod 2) W] in
/-- Enrich the existing orbit witness without choosing a different seed. -/
theorem residual_orbit_fitting_section
    (κ : GroupClass.{u}) (ρ : Representation (ZMod 2) X W) (K P : Subgroup X)
    (hs : HasFaithfulHomogeneousOrbitSection ρ K P)
    (hf : ResidualOrbitStructure κ ρ K P) : HasResidualOrbitFittingSection κ ρ K P := by
  obtain ⟨I,hI,hm,hi⟩ := hs
  obtain ⟨hk,hf',hm',hq⟩ := hf I hI
  exact ⟨I,hI,hm,hi,hk,hf',hm',hq⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
