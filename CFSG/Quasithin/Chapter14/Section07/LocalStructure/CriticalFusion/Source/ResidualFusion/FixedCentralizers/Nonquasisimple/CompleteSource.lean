module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.SourceAssembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.TwoFactorsSource
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The nonquasisimple branch of the original 14.7.68 argument

The source involution dichotomy supplies characteristic two and the full
C.2.7 hypotheses. The complete C.2.7 comparison bounds K's chief count by
one, while its actual commutator layers produce two. This excludes the
original relatively normal nonquasisimple component.

The final export obtains [U,O₂(H)]=V₁ from the genuine original13.3.2 and
12.2.2 inputs and instantiates uniqueness with the complete known-simple
A/C catalogue. Full C.2.7 remains an independently required source theorem;
no universal classification premise is silently discharged by an E-specific
specialization. Source: Aschbacher–Smith 14.7.68(2), printed pp.1071–1072.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- The actual eight-case comparison contradicts the two original core intervals. -/
theorem false_of_nonquasisimple_fixedComponent
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) : False := by
  obtain ⟨s,hs0,hs1,hs⟩ := d.exists_K_two_chief_of_point_commutator hcomm
  have hb := d.fixedComponent_chief_upper_bound_of_c27 u h c27 s hs0 hs1
  omega

/-- Apply the genuine full C.2.7 producer and the earlier source point commutator. -/
theorem false_of_nonquasisimple_fixedComponent_of_source
    (c27 : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) : False :=
  d.false_of_nonquasisimple_fixedComponent u h
    (d.fixedComponent_C27_of_source_dichotomy c27 u h)
    (d.U_core_commutator_eq_point_of_source1332 modules structural uniqueness)

/-- Full known-simple A/C discharges the universal uniqueness input. -/
theorem false_of_nonquasisimple_fixedComponent_of_known_simple_source
    (c27 : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) : False := by
  apply d.false_of_nonquasisimple_fixedComponent_of_source c27 modules structural ?_ u h
  intro X _ _ hX S B hB
  exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
    (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hX S hB
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
