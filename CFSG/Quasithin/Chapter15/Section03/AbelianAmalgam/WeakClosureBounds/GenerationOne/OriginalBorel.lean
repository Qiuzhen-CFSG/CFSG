module
public import CFSG.Quasithin.Chapter14.Section02.LargeModels
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.MinimalGeneration
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalBorel.Parity
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.SourceCases.Overlap
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Selected
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry

/-!
# The original E.2 input to the generation-one argument

The original Baumann-normalizer control makes every minimal outside H a
minimal parabolic. Proper-local inheritance supplies SQTK. The genuine source
component catalogue and generation bounds give either rank-one E-generation
or a marked binary component model at f>1, with n(H)≤f. The actual overlap is
M∩H. Its three-prime order forces f odd through the concrete Borel torus.

The output retains the full normal/exchanged structural clauses, both paired
normalizer indices, the quotient H/J and its SQTK property, and the exact
identity O²(H)=⟨K^T⟩ after inclusion into the ambient group. No equality of
generation parameters across the solvable core is needed. The later module
argument must exclude the marked-model branch to finish 15.3.65.

Source: Aschbacher--Smith 15.3.2(6), 15.3.49(4), and 15.3.65 (printed p.1152),
and E.2.2, printed pp.215--216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalBorel
open ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The marked model on the original subgroup, retaining the two residual maps. -/
structure OddModel (T : Sylow 2 G) (H M : Subgroup G) (K : Subgroup H) (f : ℕ) : Prop where
  component : K.IsCComponent
  quasisimple : IsQuasisimple (K ⧸ pCore 2 K)
  generated : K ⊔ (T : Subgroup G).subgroupOf H = ⊤
  core_le : pCore 2 H ≤ BorelReduction.sourceKernel H M
  quotient_sqtk : IsSQTK KnownSimple.IsKnownSimple (H ⧸ BorelReduction.sourceKernel H M)
  generation_le : generationParameter H ≤ f
  exponent_gt_one : 1 < f
  exponent_odd : Odd f
  cases : ReducedCases (M.subgroupOf H) K ((T : Subgroup G).subgroupOf H) f
  source_cases :
    (K.Normal ∧ SingleClauses (M.subgroupOf H) K ((T : Subgroup G).subgroupOf H) ∧
      (BenderModel (M.subgroupOf H) K f ∨
        DiagramModel (M.subgroupOf H) K ((T : Subgroup G).subgroupOf H) f)) ∨
    (¬K.Normal ∧ ExchangedClauses (M.subgroupOf H) K ((T : Subgroup G).subgroupOf H) ∧
      ExchangedModel (M.subgroupOf H) K f ∧ (normalizer (K : Set H)).index = 2 ∧
      ((normalizer (K : Set H)).subgroupOf ((T : Subgroup G).subgroupOf H)).index = 2)
  residual_eq : residual H = conjugateSpanBy (K.map H.subtype) (T : Subgroup G)

theorem exists_odd_model {T : Sylow 2 G} {H M : Subgroup G}
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple H)
    (hn : 1 < generationParameter H)
    (hthree : ¬3 ∣ Nat.card (M ⊓ H : Subgroup G)) :
    ∃ (K : Subgroup H) (f : ℕ), OddModel T H M K f := by
  obtain ⟨K,hK,hqs,hgen,f,hbound,hf,hcases⟩ :=
    Chapter14.Section02.source_large_parabolic_models hSQTK (T.subtype hH.prop.1.2) hP hn
  have hmax := BorelReduction.SourceCases.overlap_eq_minimalParabolicMax hH hP
  have hc : ReducedCases (M.subgroupOf H) K ((T : Subgroup G).subgroupOf H) f := by
    rw [hmax]
    rcases hcases with ⟨_,hs,hb|hd⟩ | ⟨_,hs,he,_,_⟩
    · exact .bender hs hb
    · exact .diagram hs hd
    · exact .exchanged hs he
  have hthree' : ¬3 ∣ Nat.card (M.subgroupOf H) := by
    have he := Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : M ⊓ H ≤ H)).toEquiv
    rw [inf_subgroupOf_right] at he
    exact fun h => hthree (he ▸ h)
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  have hquot : IsSQTK KnownSimple.IsKnownSimple (H ⧸ BorelReduction.sourceKernel H M) := by
    exact (IsSQTK.equiv (QuotientGroup.quotientMulEquivOfEq
      (BorelReduction.SourceCases.sourceKernel_eq_minimalParabolicCore hH hP))).mpr
        (ChapterE.Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple
          hSQTK (T.subtype hH.prop.1.2) hP hs)
  refine ⟨K,f,hK,hqs,hgen,BorelReduction.SourceCases.twoCore_le_sourceKernel hH hP,
    hquot,hbound,hf,(reduced_torus hc).odd hthree',hc,?_,?_⟩
  · rw [hmax]
    exact hcases
  · have hK' : ((K.map H.subtype).subgroupOf H).IsCComponent := by
      change ((K.map H.subtype).comap H.subtype).IsCComponent
      rw [comap_map_eq_self_of_injective H.subtype_injective]
      exact hK
    have hg : H = K.map H.subtype ⊔ (T : Subgroup G) := by
      have he := congrArg (fun L : Subgroup H => L.map H.subtype) hgen
      rw [Subgroup.map_sup] at he
      change (K.map H.subtype ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype) =
        (⊤ : Subgroup H).map H.subtype at he
      rw [map_subgroupOf_eq_of_le hH.prop.1.2, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at he
      exact he.symm
    exact BorelReduction.residual_eq_conjugateSpanBy_of_component hg T.isPGroup' hK'

/-- The actual positive minimum gives rank-one generation or the marked odd-field alternative. -/
theorem generation_one_or_odd_model {T : Sylow 2 G} {H M : Subgroup G}
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple H)
    (hthree : ¬3 ∣ Nat.card (M ⊓ H : Subgroup G)) :
    IsEGenerated 1 H ∨ ∃ (K : Subgroup H) (f : ℕ), OddModel T H M K f := by
  have he := ChapterE.source_minimalParabolic_generation_knownSimple hSQTK
    (T.subtype hH.prop.1.2) hP
  have hs := generation_minimum_spec_of_mem_outside hH.prop he
  by_cases hn : generationParameter H ≤ 1
  · exact Or.inl (hs.2.mono hn)
  · exact Or.inr (exists_odd_model hH hP hSQTK (by omega) hthree)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalBorel

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalBorel
open ChapterE ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_minimal_parabolic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {H : Subgroup G} (hH : H ∈ minimalSylowOutsideFamily d.T d.M) :
    ChapterB.IsMinimalParabolicOver (d.T.subtype hH.prop.1.2) ⊤ ∧
      IsSQTK KnownSimple.IsKnownSimple H := by
  have hcontrols := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have hN : normalizer (d.T : Set G) ≤ d.M :=
    (Stellmacher.normalizer_le_normalizer_baumann (d.T : Subgroup G)).trans hcontrols.2.1
  have hstar : H ∈ Chapter3.HStar (d.T : Subgroup G) d.M := hH
  have hP := Chapter3.HStar.minimalParabolic d.T d.sylow_le hstar (Or.inl hN)
  exact ⟨ChapterE.Section06.FixedPointBounds.ParabolicCartan.minimalParabolic_subtype d.T H hP,
    Chapter3.sqtk_of_mem_H hG hH.prop.1.1⟩

theorem source_odd_model_of_generation_gt_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {H : Subgroup G} (hH : H ∈ minimalSylowOutsideFamily d.T d.M)
    (hn : 1 < generationParameter H)
    (hthree : ¬3 ∣ Nat.card (d.M ⊓ H : Subgroup G)) :
    ∃ (K : Subgroup H) (f : ℕ), OddModel d.T H d.M K f := by
  obtain ⟨hP,hSQTK⟩ := source_minimal_parabolic hG d hempty hM hu hmany hH
  exact exists_odd_model hH hP hSQTK hn hthree

/-- The E.2 input to 15.3.65, with its original source premises and no model callback. -/
theorem source_generation_one_or_odd_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {H : Subgroup G} (hH : H ∈ minimalSylowOutsideFamily d.T d.M)
    (hthree : ¬3 ∣ Nat.card (d.M ⊓ H : Subgroup G)) :
    IsEGenerated 1 H ∨ ∃ (K : Subgroup H) (f : ℕ), OddModel d.T H d.M K f := by
  obtain ⟨hP,hSQTK⟩ := source_minimal_parabolic hG d hempty hM hu hmany hH
  exact generation_one_or_odd_model hH hP hSQTK hthree

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalBorel
