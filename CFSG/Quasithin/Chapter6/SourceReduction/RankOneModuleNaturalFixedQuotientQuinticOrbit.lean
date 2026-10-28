module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourFittingOriginal
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import CFSG.Quasithin.Chapter1.Section03.Terminal.Modules
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.IndexTwoConjugatePair

/-!
# The original quintic actor and the outside component orbit

The literal quintic residual normalizes the selected C-component by 1.2.1(3).
Its actual T-orbit contains an H-star member of generation parameter one.
If the quintic residual normalizes the inner Sylow of that orbit, the literal
S=O₂(XT) is Sylow in the orbit times S. The further exclusion of this last
Sylow configuration needs the generation/trapping step for O²(H)S; it is not
assumed here.

Source: Aschbacher--Smith 6.1.4, printed p.665.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The literal two-perfect quintic residual normalizes every C-component
of the original comparison maximal subgroup. -/
theorem original_hermitian_quintic_normalizes_component
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) :
    quinticResidual T L ≤ normalizer (K : Set G) := by
  obtain ⟨D,_,_,_,_,_,hXT⟩ := original_hermitian_quintic_torus h hout hm
  have hXM₁ : quinticResidual T L ≤ M₁ := le_sup_left.trans (hXT.trans hCM₁)
  let e := (subgroupOfEquivOfLe hXM₁).symm
  have hp : IsPPerfect 2 ((quinticResidual T L).subgroupOf M₁) :=
    (quinticResidual_twoPerfect T L).of_surjective e.toMonoidHom e.surjective
  have hq := Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE
    (Chapter1.mem_H_of_isTwoLocal hM₁.1)
  have hn := Chapter1.Section02.twoPerfect_normalizes_cComponent_source hq hK.2 hp
  have hn' := (map_mono (f := M₁.subtype) hn).trans
    ((K.subgroupOf M₁).le_normalizer_map M₁.subtype)
  rwa [map_subgroupOf_eq_of_le hXM₁,map_subgroupOf_eq_of_le hK.1] at hn'

/-- Original outside-component selection, with the actual quintic
normalization, orbit Sylow, and an H-star member of generation one. -/
theorem original_hermitian_exists_outside_component_orbit
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁) :
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn M₁ ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ generalizedFitting K = pCore 2 K ∧ ¬ K ≤ M ∧
      quinticResidual T L ≤ normalizer (K : Set G) ∧
      quinticResidual T L ≤ normalizer (componentOrbit K (T : Subgroup G) : Set G) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ componentOrbit K (T : Subgroup G))
        (componentOrbit K (T : Subgroup G)) ∧
      ∃ H ∈ Chapter3.HStar (T : Subgroup G) M,
        H ≤ componentOrbit K (T : Subgroup G) ⊔ (T : Subgroup G) ∧
        ChapterE.generationParameter H = 1 := by
  classical
  obtain ⟨K,hK,hq,hfit,hnot⟩ := original_hermitian_exists_component_outside h hout hm hM₁ hCM₁
  have hn := original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  have hTX := sylow_normalizes_quinticResidual (h.rankOneInput hout).sylow_normalizes
  have hnorb : quinticResidual T L ≤ normalizer (componentOrbit K (T : Subgroup G) : Set G) := by
    apply (le_iInf fun t : (T : Subgroup G) => ?_).trans (iInf_normalizer_le_normalizer_iSup _)
    exact normalizes_conjugate_of_normalizes (hTX t.property) hn
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  let K₀ := componentOrbit K (T : Subgroup G)
  have horb : K₀ ⊔ (T : Subgroup G) ≤ M₁ := by
    rw [componentOrbit_sup]
    exact sup_le hK.1 hTM₁
  have hescape : ¬ K₀ ⊔ (T : Subgroup G) ≤ M :=
    fun hh => hnot ((le_componentOrbit K (T : Subgroup G)).trans (le_sup_left.trans hh))
  let F : Set (Subgroup G) := {H | H ∈ Chapter1.HOver G (T : Set G) ∧
    ¬ H ≤ M ∧ H ≤ K₀ ⊔ (T : Subgroup G)}
  have hF : F.Nonempty := ⟨K₀ ⊔ (T : Subgroup G),
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right horb
      ⟨Chapter1.mem_H_of_isTwoLocal hM₁.1,hTM₁⟩,hescape,le_rfl⟩
  obtain ⟨H,hH⟩ := (Set.toFinite F).exists_minimalFor id F hF
  have hstar : H ∈ Chapter3.HStar (T : Subgroup G) M := by
    refine ⟨⟨hH.1.1,hH.1.2.1⟩,?_⟩
    intro Y hY hYH
    exact hH.2 ⟨hY.1,hY.2,hYH.trans hH.1.2.2⟩ hYH
  exact ⟨K,hK,hq,hfit,hnot,hn,hnorb,
    Chapter1.Terminal.sylow_inf_of_normalizes T K₀ (le_normalizer_componentOrbit K _),
    H,hstar,hH.1.2.2,h.generation_one H hstar⟩

/-- Normalization of the orbit's actual inner Sylow would force S to be
Sylow in K₀S, using the proved literal identity O₂(XT)=S. -/
theorem original_hermitian_orbit_sylow_of_normalizes
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hn : quinticResidual T L ≤ normalizer
      (((T : Subgroup G) ⊓ componentOrbit K (T : Subgroup G)) : Set G)) :
    Chapter1.IsSylowIn 2
      (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
      (componentOrbit K (T : Subgroup G) ⊔
        (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)) := by
  let K₀ := componentOrbit K (T : Subgroup G)
  let U := (T : Subgroup G) ⊓ K₀
  let S := ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hST : S ≤ (T : Subgroup G) := sup_le inf_le_left hQT
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer (le_normalizer_componentOrbit K _)).trans
      inf_normalizer_le_normalizer_inf
  have hUS : U ≤ S := by
    dsimp only [S]
    rw [←original_hermitian_quintic_sylow_core h hout hm]
    exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans le_sup_right) (sup_le hn hTU)
  obtain ⟨P,hP⟩ := Chapter1.Terminal.sylow_inf_of_normalizes T K₀
    (le_normalizer_componentOrbit K _)
  exact IsPGroup.exists_sylow_sup_of_coprime_index K₀ S
    (T.isPGroup'.to_le hST) (hST.trans (le_normalizer_componentOrbit K _))
    (P : Subgroup K₀) P.not_dvd_index (hP ▸ hUS)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
