module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOrbitCore
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.PSL3FourFaithfulExclusion

/-!
# Ratio obstructions on the original residual orbit quotient

The central quotient of any previously selected homogeneous orbit has
two-core kernel. Its faithful actor has the original PSL₃(4) component
and a two-group quotient. The faithful-action exclusion therefore gives
quadratic ratio greater than two, without assuming irreducibility of the
orbit or its restriction. Thompson replacement also excludes cubic ratio
at most one. These bounds apply to the same quotient and projection as
the generalized-Fitting calculation and the diagram obstruction.

This is a constituent input for 5.1.23, not the missing strict cubic bound
at two. The orbit-collapse argument and middle-layer fixedness remain
separate obligations. Source: Aschbacher--Smith D.3.9--10 and B.4.2--5,
as applied in 5.1.23, printed pp.645--646, `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
universe u v
variable {X : Type u} [Group X] [Finite X]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The same faithful orbit quotient satisfies both intrinsic lower bounds. -/
theorem residual_orbit_ratios
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) [K.Normal]
    (hm : ClassicalGroup.IsPSL K 3 4) (hP : IsPGroup 2 P)
    (κ : GroupClass.{u}) (hsq : IsSQTK κ K) (hkg : IsKGroup κ X)
    {I : Submodule (ZMod 2) W} (hI : IsIrrPlusWith ρ K P I) :
    let σ := orbitSectionRepresentation ρ hI
    2 < quadraticRatio (KernelQuotient.action σ) ∧
      1 < cubicRatio (KernelQuotient.action σ) := by
  let J := K ⊔ P
  let K₀ := K.subgroupOf J
  let σ := orbitSectionRepresentation ρ hI
  let q := KernelQuotient.projection σ
  let M := K₀.map q
  let : K₀.Normal := inferInstanceAs ((K.subgroupOf J).Normal)
  let : M.Normal := (inferInstance : K₀.Normal).map q
    (KernelQuotient.projection_surjective σ)
  have hgen : K₀ ⊔ P.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ J from le_sup_left)
      (show P ≤ J from le_sup_right)]
    exact subgroupOf_self _
  have hquot : IsPGroup 2 (J ⧸ K₀) :=
    quotient_isPGroup_of_sup_eq_top (P.subgroupOf J) K₀ hP.comap_subtype
      ((sup_comm _ _).trans hgen)
  have hquot' : IsPGroup 2 (KernelQuotient.Actor σ ⧸ M) :=
    hquot.of_surjective (QuotientGroup.map K₀ M q (le_comap_map q K₀))
      (QuotientGroup.map_surjective_of_surjective K₀ M q
        ((QuotientGroup.mk'_surjective M).comp (KernelQuotient.projection_surjective σ))
        (le_comap_map q K₀))
  obtain ⟨hqs,hz,_⟩ := ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm
  let := hqs
  have hq : 2 < quadraticRatio (KernelQuotient.action σ) :=
    ChapterK.Linear.Recognition.PSL3FourExclusion.quadraticRatio_gt_two_of_faithful
      (residual_orbit_sqtk ρ K P hm hP κ hsq hkg hI)
      (residual_orbit_structure ρ K P hm hP hI).2.2 hquot'
      (orbitSection_faithful_twoCore_eq_bot ρ hz hP hI) (KernelQuotient.faithful σ)
  refine ⟨hq,lt_of_not_ge ?_⟩
  intro hc
  exact not_le_of_gt hq
    (((isFFModule_iff_quadraticRatio_le_one (KernelQuotient.action σ)).mp
      (isFFModule_of_cubicRatio_le_one (KernelQuotient.action σ) hc)).trans (by norm_num))

/-- All seeds are retained, so the bounds can be used on a previously chosen orbit. -/
@[expose] def ResidualOrbitRatios
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) : Prop :=
  ∀ (I : Submodule (ZMod 2) W) (hI : IsIrrPlusWith ρ K P I),
    let σ := orbitSectionRepresentation ρ hI
    2 < quadraticRatio (KernelQuotient.action σ) ∧
      1 < cubicRatio (KernelQuotient.action σ)

theorem residual_orbit_ratios_all
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) [K.Normal]
    (hm : ClassicalGroup.IsPSL K 3 4) (hP : IsPGroup 2 P)
    (κ : GroupClass.{u}) (hsq : IsSQTK κ K) (hkg : IsKGroup κ X) :
    ResidualOrbitRatios ρ K P := by
  intro I hI
  exact residual_orbit_ratios ρ K P hm hP κ hsq hkg hI

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
