module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Source
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Comparison
public import CFSG.Quasithin.Chapter13.Section07.SpanGrowth
public import CFSG.Quasithin.Chapter13.Section05.PointAction

/-!
# Original-source solvable exclusion and its Fitting consumers

The natural point-fixer action proves the flag-normalizer bound from the
original13.5.4 centralizer containment. The source13.7 commutator theorem
supplies [V₃,Q_H]=V₁ and noncentrality of V_H/U_H from the original
noncentral action on O₂(G₁). Thus the selected critical geometry and the
entire solvable-overgroup contradiction are applied without any geometric
conclusion as input.

The immediate13.8.14--15 component consumers and covered13.8.21 comparison
use that proved containment. The independent earlier inputs are the genuine
F.9 applicability, covered normalizer control13.2.2(9), the two ambient
13.5.4 assertions and universal13.3.9. The abelian full span is the standing
13.7.8 hypothesis retained in LocalSetup.
Source: Aschbacher--Smith,13.8.13--15,21, printed pp.950--951,957.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree
open Geometry Geometry.ExternalComponentAction Geometry.CoveredProduct.ResidualPlacement
open SolvableExclusion
variable {G:Type*} [Group G] [Finite G]
 {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
 (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
 (hF9all:∀J∈Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
 (hN:Nonempty ((L⧸pCore 2 L)≃*Atlas.Codes.HexEvenAutomorphisms)→normalizer (zero L:Set G)≤M)
 (hcentral:centralizer (V₃:Set G)≤M⊓normalizer (V:Set G))
 (hcomm:⁅V₃,G₁.pCoreIn 2⁆≠⊥)
 (hsource:Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
include d hF9all hN hcentral hcomm hsource

theorem solvable_overgroup_of_earlier
    (H:Subgroup G) (hLT:one L T V₁⊔(T:Subgroup G)≤H) (hHG:H≤G₁)
    (hs:Group.IsSolvable H) : H≤M := by
  let dn:=localNaturalSetup d
  have hflag:normalizer (V₁:Set G)⊓normalizer (V₃:Set G)≤M⊓normalizer (V:Set G) := by
    simpa only [dn.first_normalizer] using Section05.PointAction.normalizer_intersection_source dn hcentral
  apply solvable_overgroup_le d hN hflag hsource hF9all ?_ ?_ hLT hHG hs
  · intro J hJ
    exact (Section07.source_commutator_conclusions dn (hF9all J hJ) hJ.2.1 hcomm).2.1.symm
  · intro J hJ
    let := d.uh_elementary hJ
    exact Section07.source_noncentral_VH_quotient_of_earlier_geometry dn
      (hF9all J hJ) inferInstance hJ.2.1 hJ.2.2 (hflag.trans inf_le_left) hcomm

theorem source_fitting_center (hH:H∈Source.Hz (one L T V₁) T G₁ M) :
    fittingSubgroup (Source.Hstar H) =
      (center (pResidual 2 (Source.Hstar H))).map (pResidual 2 (Source.Hstar H)).subtype :=
  LocalFitting.fitting_center d hH hsource
    (solvable_overgroup_of_earlier d hF9all hN hcentral hcomm hsource)

theorem source_component_fitting (hH:H∈Source.Hz (one L T V₁) T G₁ M)
    (K:Subgroup G) (hK:(K.subgroupOf H).IsCComponent) :
    fittingSubgroup (Source.Hstar H) ≤ centralizer (Source.starImage H K:Set (Source.Hstar H)) ∧
      IsQuasisimple (Source.starImage H K) :=
  LocalFitting.component_fitting d hH hsource
    (solvable_overgroup_of_earlier d hF9all hN hcentral hcomm hsource) K hK

theorem source_component_orbit (hH:H∈Source.Hz (one L T V₁) T G₁ M)
    (K:Subgroup G) (hK:(K.subgroupOf H).IsCComponent) :
    (K.subgroupOf H).Normal ∨ (normalizer (K.subgroupOf H:Set H)).index = 2 :=
  LocalFitting.component_orbit d hH hsource
    (solvable_overgroup_of_earlier d hF9all hN hcentral hcomm hsource) K hK

theorem source_exists_component (hH:H∈Source.Hz (one L T V₁) T G₁ M) :
    ∃K:Subgroup G, K≤H ∧ (K.subgroupOf H).IsCComponent ∧
      ¬K≤M ∧ IsQuasisimple (Source.starImage H K) :=
  LocalFitting.exists_source_component d hH hsource
    (solvable_overgroup_of_earlier d hF9all hN hcentral hcomm hsource)

theorem source_covered_comparison {K:Subgroup G} {κ:GroupClass}
    (components:RankReduction.SourceSetup κ H K (one L T V₁) M G₁ T)
    (models:RankReduction.SmallQuotient (K⧸pCore 2 K))
    (hcovered:Nonempty ((L⧸pCore 2 L)≃*Atlas.Codes.HexEvenAutomorphisms)) : one L T V₁≤K := by
  have hH:=components.local_overgroup
  have hflag:normalizer (V₁:Set G)⊓normalizer (V₃:Set G)≤M⊓normalizer (V:Set G) := by
    simpa only [(localNaturalSetup d).first_normalizer] using
      Section05.PointAction.normalizer_intersection_source (localNaturalSetup d) hcentral
  let := d.uh_elementary hH
  exact LocalFitting.covered_comparison d (hF9all H hH) components models hcovered (hN hcovered)
    hsource (solvable_overgroup_of_earlier d hF9all hN hcentral hcomm hsource)
    (Section07.source_noncentral_VH_quotient_of_earlier_geometry (localNaturalSetup d)
      (hF9all H hH) inferInstance hH.2.1 hH.2.2 (hflag.trans inf_le_left) hcomm)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
