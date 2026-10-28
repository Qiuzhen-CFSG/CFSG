module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourInnerThompson
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneSource
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson.KnownSimple

/-!
# E.6.26 traps the actual inner-Sylow overgroups

The literal S=(T∩L)O₂(LT) contains the full-module Sylow centralizer and
has J₁(S) centralizing that same module. The proved hyperplane bound gives
r(G,R₂(LT))>1. Thus the proved known-simple E.6.26 applies to every actual
overgroup of generation parameter at most one with Sylow subgroup S.

Source: Aschbacher--Smith 6.1.4, printed p.665.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H M₁ : Subgroup G} {n s : ℕ} [NeZero s]
local instance overgroupsFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance overgroupsBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The original S-family containment, with the actual numerical E-generation
theorem. T-invariance is not needed for this containment. -/
theorem full_reduced_hermitian_inner_sylow_overgroup_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (hM₁ : IsMaximalTwoLocal M₁) (hH : H ≤ M₁)
    (hSyl : Chapter1.IsSylowIn 2
      (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) H)
    (hgen : ChapterE.generationParameter H ≤ 1) :
    H ≤ M ∧ normalizer
      (((((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) : Subgroup G) : Set G) ≤ M := by
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let S := ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨P,hP⟩ := hSyl
  have hE := full_reduced_hermitian_hypothesisE61 h hm
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    ((h.simpleQTKE.twoLocal_sqtk hM₁.1).subgroup (H.subgroupOf M₁)).knownSimple_of_equiv
      (subgroupOfEquivOfLe hH)
  have hQ : ChapterE.Section06.sylowCentralizer (T : Subgroup G) B ≤ S := by
    change (T : Subgroup G) ⊓ centralizer (B : Set G) ≤ S
    rw [full_reduced_hermitian_sylow_centralizer h hm]
    exact le_sup_right
  have hST : S ≤ (T : Subgroup G) := sup_le inf_le_left hQT
  have hJ : ChapterB.thompsonJ S 1 ≤ centralizer (B : Set G) :=
    (h.reduced_enlargement.rankOneInput hout).hermitian_inner_thompson_one_centralizes hm hs
  simpa only [hP] using
    ChapterE.Section06.FixedPointBounds.SylowThompson.source_E_6_26_knownSimple
      hE (by decide : 0 < 1) H P hSQ hgen (hP.symm ▸ hQ) (hP.symm ▸ hST)
      (full_reduced_hermitian_one_lt_globalR h hout hm hs) (hP.symm ▸ hJ)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
