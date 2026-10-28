module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationPreparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.LocalTransfer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.LocalSections
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Inputs

/-!
# The local actor and component for the binary model sieve

The group to which B.5.6 applies is J* = ⟨A^H⟩*, acting on the actual
U_H/Z section. Its SQTK cover is the subgroup ⟨A^H⟩ inside H. The explicit
component-generation hypothesis (i) makes J*, as well as J, perfect.
The selected C-component remains a C-component in J*, and its intrinsic
two-core quotient is identified with that literal relative subgroup.

These are application hypotheses and quotient comparisons, not the FF
classification or a proof of ordinary quasisimplicity. In particular no
identification of ⟨L^T⟩ with L is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.3,
printed p.104, and 15.3.49(i)–(l), printed pp.1143–1144.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The selected component, regarded as a subgroup of the actual FF actor. -/
abbrev starComponent (H A L : Subgroup G) : Subgroup (starImage H (localSpan A H)) :=
  (starImage H L).subgroupOf (starImage H (localSpan A H))

/-- The literal SQTK quotient presentation required by the shared B.5.6 interface. -/
noncomputable def starSpanSQTKQuotient {κ : GroupClass.{u}}
    (H A : Subgroup G) (hH : IsSQTK κ H) :
    SQTKQuotient κ (starImage H (localSpan A H)) where
  Cover := (localSpan A H).subgroupOf H
  kernel := (FactorGeneration.spanStarProjection H A).ker
  sqtk := FactorGeneration.spanStarCover_sqtk H A hH
  equiv := FactorGeneration.spanStarQuotientEquiv H A

/-- All of B.5.3 and a nontrivial FF witness, on the original section action. -/
theorem starSpanFFHypothesis {κ : GroupClass.{u}}
    (H ZS Z A : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hH : IsSQTK κ H) (hAH : A ≤ H)
    (hbest : IsBestOffender action.representation (starImage H A)) :
    FFHypothesis κ (action.representation.comp (starImage H (localSpan A H)).subtype) ∧
      IsFFModule (action.representation.comp (starImage H (localSpan A H)).subtype) := by
  obtain ⟨hfinite, hfaithful, hcore, hgenerated, _, hFF⟩ :=
    FactorGeneration.star_span_classification_hypotheses H ZS Z A action hH hAH hbest
  exact ⟨⟨hfinite, hfaithful, hcore, hgenerated, ⟨starSpanSQTKQuotient H A hH⟩⟩, hFF⟩

/-- The selected conjugate supplies the actual B.5.3 input, retaining its
quadratic best-offender property and the equality of the two normal closures. -/
theorem selected_starSpanFFHypothesis {κ : GroupClass.{u}}
    (H ZS Z Vgamma A : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hH : IsSQTK κ H) (hVH : Vgamma ≤ H) (h : H)
    (hselected : A = FactorGeneration.selectedConjugate H Vgamma h)
    (hbest : IsBestOffender action.representation (starImage H Vgamma))
    (hquad : IsQuadratic action.representation (starImage H Vgamma)) :
    A ≤ H ∧ localSpan A H = localSpan Vgamma H ∧
      IsBestOffender action.representation (starImage H A) ∧
      IsQuadratic action.representation (starImage H A) ∧
      FFHypothesis κ (action.representation.comp (starImage H (localSpan A H)).subtype) ∧
      IsFFModule (action.representation.comp (starImage H (localSpan A H)).subtype) := by
  subst A
  have hAH := FactorGeneration.selectedConjugate_le H Vgamma hVH h
  obtain ⟨hbest', hquad'⟩ :=
    FactorGeneration.selectedConjugate_offender H ZS Z Vgamma action hVH h hbest hquad
  exact ⟨hAH, FactorGeneration.selectedConjugate_span H Vgamma h, hbest', hquad',
    starSpanFFHypothesis H ZS Z _ action hH hAH hbest'⟩

omit [Finite G] in
/-- The explicit component-generation assertion (i) makes the unquotiented span perfect. -/
theorem span_isPerfect (H A : Subgroup G)
    (hgen : (cComponentLayer (localSpan A H)).map (localSpan A H).subtype =
      localSpan A H) : Group.IsPerfect (localSpan A H) := by
  let := cComponentLayer_isPerfect (G := localSpan A H)
  have h := Group.IsPerfect.map (H := cComponentLayer (localSpan A H))
    (localSpan A H).subtype
  rwa [hgen] at h

omit [Finite G] in
/-- Perfectness descends to J*. It is not inferred by lifting through a two-core. -/
theorem starSpan_isPerfect (H A : Subgroup G) (hAH : A ≤ H)
    (hgen : (cComponentLayer (localSpan A H)).map (localSpan A H).subtype =
      localSpan A H) : Group.IsPerfect (starImage H (localSpan A H)) := by
  let := span_isPerfect H A hgen
  let e := (subgroupOfEquivOfLe (conjugateSpanBy_le_self hAH)).symm
  let : Group.IsPerfect ((localSpan A H).subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.ofSurjective (FactorGeneration.spanStarProjection_surjective H A)

/-- The selected relative C-component survives the two-core quotient. -/
theorem starComponent_isCComponent (H A L : Subgroup G) (hAH : A ≤ H)
    (hLJ : L ≤ localSpan A H) (hL : (L.subgroupOf (localSpan A H)).IsCComponent) :
    (starComponent H A L).IsCComponent := by
  have hc := localSpan_component_isCComponent A H L hAH hLJ hL
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact (hc.map_quotient (pCore 2 H)).subgroupOf (map_mono (comap_mono hLJ))

/-- Identify L/O₂(L) with the literal component subgroup of J*, not just an abstract section. -/
noncomputable def intrinsicComponentEquiv (H A L : Subgroup G) (hAH : A ≤ H)
    (hLJ : L ≤ localSpan A H) (hL : (L.subgroupOf (localSpan A H)).IsCComponent) :
    (L ⧸ pCore 2 L) ≃* starComponent H A L :=
  (componentStarEquiv H L (hLJ.trans (conjugateSpanBy_le_self hAH))
    (localSpan_component_isCComponent A H L hAH hLJ hL)).trans
      (subgroupOfEquivOfLe (map_mono (comap_mono hLJ))).symm

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ModelSieve
