module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.SourceFusion

/-!
# The original fixed-centralizer component selection

The full source containment theorem constructs the actual normal C-component
of C_G(u) containing K. Its Sylow subgroup is obtained from the genuine
C.1.26 implication applied to the original two chief factors. The source
residual-normalizer theorem then makes the selected component strictly
larger than K and forces it outside H.

No A.3.8 model list, component selection, normality, fixed Sylow, or
characteristic-subgroup witness is assumed in the final export. The odd
component quotient reduction and its subsequent classification are separate.
Source: Aschbacher–Smith 14.7.68(2), printed p.1071.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 ResidualNormalizer Rechoice.Goldschmidt
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- The literal component of C_G(u), with A.3 containment and normality proved. -/
theorem exists_fixedComponent_of_known_simple_source
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u)) :
    ∃ Lu : Subgroup G, Lu ≤ d.fixedCentralizer u ∧
      (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent ∧ K F ≤ Lu ∧
      (Lu.subgroupOf (d.fixedCentralizer u)).Normal := by
  obtain ⟨S,hS⟩ := hsyl
  have hloc : (K F).subgroupOf (d.fixedCentralizer u) ∈
      Chapter1.L (d.fixedCentralizer u) (S : Subgroup (d.fixedCentralizer u)) := by
    rw [← Chapter1.mem_L_map_iff (d.fixedCentralizer u).subtype
      (d.fixedCentralizer u).subtype_injective,
      map_subgroupOf_eq_of_le (d.K_le_fixedCentralizer u hu),hS]
    exact d.K_mem_fixedLocalFamily u hu hfix
  have hSnorm : (S : Subgroup (d.fixedCentralizer u)) ≤
      normalizer ((K F).subgroupOf (d.fixedCentralizer u) : Set (d.fixedCentralizer u)) := by
    rw [← subgroupOf_normalizer_eq (d.K_le_fixedCentralizer u hu)]
    intro s hs
    have hsT : (s : G) ∈ (T : Subgroup G) :=
      (show (s : G) ∈ d.fixedSylow u by rw [← hS]; exact mem_map_of_mem _ hs).1
    exact H_normalizes_K F (F.invariant 1 hsT)
  obtain ⟨D,⟨hD,hKD,hn⟩,_⟩ := Chapter1.Section02.lemma_1_2_4_containment_normality_source
    (d.fixedCentralizer_quotient_sqtk u hne) S hloc hSnorm
  have hmap : (D.map (d.fixedCentralizer u).subtype).subgroupOf (d.fixedCentralizer u) = D :=
    comap_map_eq_self_of_injective (d.fixedCentralizer u).subtype_injective _
  refine ⟨D.map (d.fixedCentralizer u).subtype,map_subtype_le _,hmap.symm ▸ hD,?_,
    hmap.symm ▸ hn⟩
  simpa only [map_subgroupOf_eq_of_le (d.K_le_fixedCentralizer u hu)] using
    map_mono (f := (d.fixedCentralizer u).subtype) hKD

/-- Original source selection, using the genuine earlier C.1.26 implication. -/
theorem exists_larger_fixedComponent_of_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (baumann : LocalControl.Earlier14710.{u}) (weakClosure : Theorem14731.{u})
    (choices : DistinguishedPairs.{u}) (source : C126Source KnownSimple.IsKnownSimple choices)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (hout : ¬ d.fixedCentralizer u ≤ F.H) :
    Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u) ∧
      ∃ Lu : Subgroup G, Lu ≤ d.fixedCentralizer u ∧
        (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent ∧ K F < Lu ∧
        (Lu.subgroupOf (d.fixedCentralizer u)).Normal ∧ ¬ Lu ≤ F.H := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S B hB
    exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hX S hB
  obtain ⟨hNK,hmax⟩ :=
    d.normalizer_K_eq_H_of_known_simple_source structural faithful modules baumann weakClosure
  have hcomm := d.U_core_commutator_eq_point_of_source1332 modules structural uniqueness
  have hsyl := d.fixedSylow_isSylow_of_point_commutator choices source hcomm u hu hne hfix hmax
  obtain ⟨Lu,hLu,hc,hKLu,hn⟩ := d.exists_fixedComponent_of_known_simple_source u hu hne hfix hsyl
  have hLH := d.fixedComponent_not_le_H u hu hNK hout hLu hc hKLu hn
  exact ⟨hsyl,Lu,hLu,hc,lt_of_le_of_ne hKLu (fun he => hLH (he ▸ K_le_H F)),hn,hLH⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
