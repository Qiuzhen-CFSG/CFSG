module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.CompleteSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.CompleteSource

/-!
# Both component branches of the original14.7.68 argument

Split the actual selected component according to quasisimplicity. The
quasisimple branch constructs and excludes the marked Rudvalis cover; the
other branch applies the genuine full C.2.7 producer and contradicts the
original chief factors. The same component, involution, Sylow and normalizer
are retained throughout.

The separate earlier quotient reduction Lᵤ/O₂(Lᵤ) quasisimple remains explicit.
Its source producer must use the original critical elementary subgroup as
explained in Characteristic.OddAlternatives; the intrinsic generic odd-action
shortcut is false. Full universal C.2.7 also remains an earlier input.
Source: Aschbacher–Smith14.7.68(2), printed pp.1071–1072.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- Both component contradictions, with all model, cover and chief premises discharged. -/
theorem false_of_fixedComponent_of_known_simple_source
    (c27 : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hNK : normalizer (K F : Set G) = F.H)
    (hmax : IsMaximalTwoLocal F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (Lu : Subgroup G) (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hKLu : K F < Lu) (hout : ¬ Lu ≤ F.H)
    (hq : IsQuasisimple (Lu ⧸ pCore 2 Lu)) : False := by
  by_cases hqs : IsQuasisimple Lu
  · exact d.false_of_quasisimple_fixedComponent_of_known_simple_source modules structural
      u hu hne hfix hNK hmax hsyl Lu hLu hc hn hKLu hout hqs
  · let h : Nonquasisimple.Case d u Lu :=
      ⟨hu,hne,hfix,hNK,hmax,hsyl,hLu,hc,hKLu,hn,hout,hqs,hq⟩
    exact d.false_of_nonquasisimple_fixedComponent_of_known_simple_source c27 modules structural u h
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
