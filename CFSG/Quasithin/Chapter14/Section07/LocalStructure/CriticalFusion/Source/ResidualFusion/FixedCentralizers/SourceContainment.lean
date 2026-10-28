module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.ComponentExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.OddFitting
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.SourceSelection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic.FivePointSource
/-!
# Original fixed-element centralizer containment

The actual five-point quotient supplies the characteristic subgroup and hence
Sylow control in C_G(u). Source component selection gives a normal component
containing K. The quasisimple case is excluded by the completed marked Ru
argument. Otherwise C.2.6 and A.3.6 prove quotient quasisimplicity, so the
remaining C.2.7 comparison contradicts the original two chief factors.

No Sylow witness, component choice, quotient model, odd-action statement or
critical reversal is an added premise. The genuine earlier structural,
faithful/module, local-control, weak-closure and full C.2.7 implications are
retained for their source producers.
Source: Aschbacher–Smith 14.7.68(2), printed pp.1071–1072.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer Rechoice.Goldschmidt
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedCentralizer_le_H_of_original_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumann : LocalControl.Earlier14710.{u}) (weakClosure : Theorem14731.{u})
    (c27 : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) : d.fixedCentralizer u ≤ F.H := by
  classical
  by_contra hout
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S B hB
    exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hX S hB
  obtain ⟨hNK,hmax⟩ :=
    d.normalizer_K_eq_H_of_known_simple_source structural faithful modules baumann weakClosure
  have hcomm := d.U_core_commutator_eq_point_of_source1332 modules structural uniqueness
  have hsyl := d.fixedSylow_isSylow_fivePoint_source hcomm u hu hne hfix hmax
  obtain ⟨Lu,hLu,hc,hKLu,hn⟩ := d.exists_fixedComponent_of_known_simple_source u hu hne hfix hsyl
  have hLH := d.fixedComponent_not_le_H u hu hNK hout hLu hc hKLu hn
  have hlt : K F < Lu := lt_of_le_of_ne hKLu (fun he => hLH (he ▸ K_le_H F))
  by_cases hqs : IsQuasisimple Lu
  · exact d.false_of_quasisimple_fixedComponent_of_known_simple_source modules structural
      u hu hne hfix hNK hmax hsyl Lu hLu hc hn hlt hLH hqs
  · exact d.false_of_nonquasisimple_fixedComponent_of_known_simple_source c27 modules structural u
      (d.fixedComponent_case_of_source u hu hne hfix hmax hNK hsyl hLu hc hlt hn hLH hqs)
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
