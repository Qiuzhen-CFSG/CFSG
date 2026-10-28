module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.RudvalisSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.EvenCovers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.RudvalisNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion.ModuleSeparation
public import CFSG.Quasithin.Chapter1.SourceInputs
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Excluding the original quasisimple fixed component

Full marked1.1.5 on the original component gives its source action. The
exceptional two-cover exclusions and the complete sporadic comparison select
the exact Rudvalis cover. The already proved original eight placement and
unique-complement argument then identify its V-normalizer and contradict
the original Sylow configuration. Module separation is constructed, and the
full known-simple A/B/C catalogue supplies1.1.5 and uniqueness internally.

Source: Aschbacher–Smith14.7.68(2), printed p.1071. Only the independent
original12.2.2/13.3.2 inputs remain in the final source export.
-/

public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Theory.GroupTheory Chapter12.Section08 ClassificationModels
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedRudvalisCover_of_original_component
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hNK : normalizer (K F : Set G) = F.H)
    (hmax : IsMaximalTwoLocal F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (Lu : Subgroup G) (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hKLu : K F < Lu) (hout : ¬ Lu ≤ F.H) (hq : IsQuasisimple Lu)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) : Nonempty (d.FixedRudvalisCover u Lu) := by
  have h115 : ∀ (H : Subgroup G) (S : Sylow 2 H) (M : Subgroup G) (z : G),
      Chapter1.Lemma115Hypotheses H S M z →
        ∀ A : Subgroup H, IsComponent H A → HasModelAction115 A z := by
    intro H S M z h A hA
    exact (Chapter1.lemma_1_1_5_three_source d.counterexample.qtke
      (fun X _ _ => ChapterA.Section02.theoremsABC_knownSimple (G := X)) H S M z h A hA).2.2
  obtain ⟨α,ha,hm⟩ := d.fixedComponent_evenModelActions h115 d.U_eq_commutator_K u hne
    hmax hsyl hLu hn hq hKLu.le
  rcases hm with ⟨hzn,hze,hm,hi⟩ | ⟨name,hname,⟨e⟩,htwo⟩
  · let c : EvenCoverSieve.Case d u Lu α :=
      ⟨hu,hne,hfix,hNK,hmax,hsyl,hLu,hc,hn,hKLu,hout,hq,d.U_eq_commutator_K,ha,hzn,hze,hi⟩
    exact (c.not_twoCover hm).elim
  · let c : SporadicSieve.Case d u Lu α name :=
      ⟨hu,hne,hfix,hNK,hmax,hsyl,hLu,hc,hn,hKLu,hout,hq,d.U_eq_commutator_K,ha,hname,htwo⟩
    exact d.exists_fixedRudvalisCover_of_sporadic u e c hcomm

theorem false_of_quasisimple_fixedComponent_of_point_commutator
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hNK : normalizer (K F : Set G) = F.H)
    (hmax : IsMaximalTwoLocal F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (Lu : Subgroup G) (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hKLu : K F < Lu) (hout : ¬ Lu ≤ F.H) (hq : IsQuasisimple Lu)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) : False := by
  obtain ⟨r⟩ := d.fixedRudvalisCover_of_original_component u hu hne hfix hNK hmax
    hsyl Lu hLu hc hn hKLu hout hq hcomm
  exact d.false_of_fixedRudvalisCover (Rechoice.SourceCompletion.moduleSeparation d)
    structural u hu hne hfix hNK hmax hsyl Lu hLu hc hn hKLu hout hq r
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Theory.GroupTheory Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- The genuine earlier module and structure inputs discharge the point commutator. -/
theorem false_of_quasisimple_fixedComponent_of_known_simple_source
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hNK : normalizer (K F : Set G) = F.H)
    (hmax : IsMaximalTwoLocal F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    (Lu : Subgroup G) (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal)
    (hKLu : K F < Lu) (hout : ¬ Lu ≤ F.H) (hq : IsQuasisimple Lu) : False := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S B hB
    exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hX S hB
  exact d.false_of_quasisimple_fixedComponent_of_point_commutator structural u hu hne
    hfix hNK hmax hsyl Lu hLu hc hn hKLu hout hq
    (d.U_core_commutator_eq_point_of_source1332 modules structural uniqueness)
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
