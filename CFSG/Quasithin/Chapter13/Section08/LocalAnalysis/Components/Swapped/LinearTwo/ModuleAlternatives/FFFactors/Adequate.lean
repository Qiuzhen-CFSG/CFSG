module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.ClassifiedGroups.Adequate

/-!
# The literal maximal-section application of adequate B.5.6

The corrected classifier is applied to the faithful offender actor of the
original maximal source quotient. Two actual components select the full
two-factor record. Intrinsic module recognition and transport then give the
original marked commutator factors and both exchanges by the specified t.
No legacy triple-six offender clause or outer fixed-space splitting is used.

The B.5 implication and the genuine F.9.18 FF premise remain earlier inputs.
Source: Aschbacher–Smith, B.5.6(3), p.105; 13.8.16(1), p.952
(combined manuscript, 1 March 2004).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
open ComponentSieve.AlternatingAndLinear.FourStructure
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
    (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (ChiefFactors.SourceSpace H V₃ V₁))
    (hρ : ChiefFactors.IsSourceAction H V₃ V₁ ρ)

include hρ

/-- Apply the complete universal B.5.6 contract to the literal maximal source
quotient. The genuine FF condition from F.9.18 is explicit. All B.5.3
hypotheses, including the SQTK cover and offender generation, are proved.
This does not yet select its two-factor alternative. -/
theorem source_section_classification_of_adequate {𝒦 : GroupClass.{u}}
    (classification : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} 𝒦) (hSQTK : IsSQTK 𝒦 H)
    (K L₁ T : Subgroup G)
    (hH : H = conjugateSpanBy K T ⊔ (L₁ ⊔ T))
    (hL : L₁ ≤ conjugateSpanBy K T)
    (hLN : L₁ ≤ normalizer (V₃ : Set G)) (hline : V₁ ≤ V₃)
    (hseed : V₃ ≤ ⁅L₁, V₃⁆ ⊔ V₁)
    (W : Subrepresentation ρ)
    (hW : ¬ subspaceCommutator ρ ⊤ (Source.starImage H (conjugateSpanBy K T)) ≤ W.toSubmodule)
    (hmax : ∀ Y : Subrepresentation ρ, W ≤ Y →
      ¬ subspaceCommutator ρ ⊤ (Source.starImage H (conjugateSpanBy K T)) ≤ Y.toSubmodule → Y = W)
    (hff : IsFFModule (imageRepresentation W.quotientRepresentation)) :
    FFHypothesis 𝒦 (offenderRepresentation (imageRepresentation W.quotientRepresentation)) ∧
      ProjectiveLine.AdequateSourceAlternative (offenderRepresentation (imageRepresentation W.quotientRepresentation)) ∧
      IsFFModule (offenderRepresentation (imageRepresentation W.quotientRepresentation)) := by
  have hfull := source_moved_eq_top H V₃ V₁ ρ hρ K L₁ T hH hL hLN hline hseed
  let : W.quotientRepresentation.IsIrreducible :=
    maximal_component_section_irreducible ρ W _ hfull hW hmax
  let : Module.Finite (ZMod 2) (ChiefFactors.SourceSpace H V₃ V₁) :=
    Module.Finite.of_finite
  have hyp := irreducible_offender_hypothesis W.quotientRepresentation
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _) hSQTK
  exact ⟨hyp, classification _ _ _ hyp,
    offender_isFFModule _ hff⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
universe u
variable {D V : Type u} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- Assemble the full classification and intrinsic recognition on the
faithful offender actor, preserving the original marked subgroups. -/
theorem markedFactors_of_classification_of_adequate [Finite D] {𝒦 : GroupClass.{u}}
    (hyp : FFHypothesis 𝒦 (offenderRepresentation (imageRepresentation ρ)))
    (hc : ProjectiveLine.AdequateSourceAlternative (offenderRepresentation (imageRepresentation ρ)))
    (hfaith : Function.Injective ρ)
    (hfix : (offenderRepresentation (imageRepresentation ρ)).invariants = ⊥)
    (A B N : Subgroup D) (hcompA : IsComponent D A) (hcompB : IsComponent D B)
    (hne : A ≠ B) (hjoin : A ⊔ B = N)
    (e : A × B ≃* N) (he : ∀ a b, (e (a, b) : D) = (a : D) * b)
    (hfull : subspaceCommutator ρ ⊤ N = ⊤)
    (hN : actionSubgroup ρ N ≤ offenderActor (imageRepresentation ρ))
    {n : ℕ} (hn : 2 ≤ n) (hmA : ClassicalGroup.IsPSL A 2 (2 ^ n))
    (hmB : ClassicalGroup.IsPSL B 2 (2 ^ n)) : MarkedFactors ρ A B n := by
  let J := offenderActor (imageRepresentation ρ)
  let σ := offenderRepresentation (imageRepresentation ρ)
  have hA : actionSubgroup ρ A ≤ J := (Subgroup.map_mono (hjoin ▸ le_sup_left)).trans hN
  have hB : actionSubgroup ρ B ≤ J := (Subgroup.map_mono (hjoin ▸ le_sup_right)).trans hN
  let A' := (actionSubgroup ρ A).subgroupOf J
  let B' := (actionSubgroup ρ B).subgroupOf J
  have hA' := marked_isComponent ρ hfaith A hcompA hA
  have hB' := marked_isComponent ρ hfaith B hcompB hB
  have hinj : Function.Injective (actionHom ρ) := by
    intro a b h
    exact hfaith (congrArg (imageRepresentation ρ) h)
  have hne' : A' ≠ B' := by
    intro hh
    have hh' := congrArg (Subgroup.map J.subtype) hh
    rw [map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB] at hh'
    exact hne (Subgroup.map_injective hinj hh')
  have hjoin' : A' ⊔ B' = (actionSubgroup ρ N).subgroupOf J := by
    rw [← hjoin]
    dsimp only [A', B', actionSubgroup]
    rw [Subgroup.map_sup]
    exact (subgroupOf_sup hA hB).symm
  have hfull' : subspaceCommutator σ ⊤ (A' ⊔ B') = ⊤ := by
    rw [hjoin', actionImage_marked_commutator ρ N hN, hfull]
  obtain ⟨c, ha, hb⟩ := ClassifiedGroups.exists_marked_twoFactorCase_of_adequate σ hyp hc hA' hB' hne' hfull'
  have hmA' := hmA.of_mulEquiv (markedActorEquiv ρ hfaith A hA).symm
  have hmB' := hmB.of_mulEquiv (markedActorEquiv ρ hfaith B hB).symm
  have recA := MarkedModels.sourceFactorCase_recognition σ hfix c.firstCase hA' ha hn hmA'
  have recB := MarkedModels.sourceFactorCase_recognition σ hfix c.secondCase hB' hb hn hmB'
  obtain ⟨hd, hx, hy⟩ := marked_product_direct_sum_of_classified_factors ρ hfix c
    A B N e he hfull hA hB ha hb
  exact ⟨hd, factorModule_of_offender_actor ρ hfaith A hA recA.2,
    factorModule_of_offender_actor ρ hfaith B hB recB.2, hx, hy⟩

open ComponentSieve.AlternatingAndLinear.FourStructure
variable {G : Type u} [Group G] [Finite G]
    (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (σ : Representation (ZMod 2) (Source.Hstar H) (ChiefFactors.SourceSpace H V₃ V₁))
    (hσ : ChiefFactors.IsSourceAction H V₃ V₁ σ)

include hσ

/-- The conditional source case-(a) deduction on the literal maximal quotient.
The full universal classification and the FF-section condition remain inputs.
The product and exchange operators retain both actual component inclusions. -/
theorem source_section_marked_factors_of_adequate {𝒦 : GroupClass.{u}}
    (classification : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} 𝒦) (hSQTK : IsSQTK 𝒦 H)
    (K L₁ T : Subgroup G)
    (hH : H = conjugateSpanBy K T ⊔ (L₁ ⊔ T)) (hL : L₁ ≤ conjugateSpanBy K T)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : IsQuasisimple (Source.starImage H K)) (hT : IsPGroup 2 T)
    (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
    (t : H) (ht : (t : G) ∈ T) (hm : (t : G) ∉ normalizer (K : Set G))
    {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    (hLN : L₁ ≤ normalizer (V₃ : Set G)) (hline : V₁ ≤ V₃)
    (hseed : V₃ ≤ ⁅L₁, V₃⁆ ⊔ V₁)
    (W : Subrepresentation σ)
    (hW : ¬ subspaceCommutator σ ⊤ (Source.starImage H (conjugateSpanBy K T)) ≤ W.toSubmodule)
    (hmax : ∀ Y : Subrepresentation σ, W ≤ Y →
      ¬ subspaceCommutator σ ⊤ (Source.starImage H (conjugateSpanBy K T)) ≤ Y.toSubmodule → Y = W)
    (hff : IsFFModule (imageRepresentation W.quotientRepresentation)) :
    ∃ e : Source.starImage H K × Source.starImage H (K.conjBy (t : G)) ≃*
        Source.starImage H (conjugateSpanBy K T),
      (∀ a b, (e (a, b) : Source.Hstar H) = (a : Source.Hstar H) * b) ∧
      MarkedFactors W.quotientRepresentation
        (Source.starImage H K) (Source.starImage H (K.conjBy (t : G))) n ∧
      (subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H (K.conjBy (t : G)))).map
        (operator W.quotientRepresentation (QuotientGroup.mk' (pCore 2 H) t)).toLinearMap =
          subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H K) ∧
      (subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H K)).map
        (operator W.quotientRepresentation (QuotientGroup.mk' (pCore 2 H) t)).toLinearMap =
          subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H (K.conjBy (t : G))) := by
  have hKH : K ≤ H := (le_conjugateSpanBy K T).trans (by rw [hH]; exact le_sup_left)
  have hTH : T ≤ H := by rw [hH]; exact le_sup_right.trans le_sup_right
  have hspan := orbit_eq_two_conjugates H K T hKH hTH hi ht hm
  obtain ⟨hJH, hJ⟩ := conjugate_isCComponent H K hKH hK t.property
  let c := starConjugateEquiv H K hKH t.property
  let := hq
  have hqJ : IsQuasisimple (Source.starImage H (K.conjBy (t : G))) :=
    IsQuasisimple.of_mulEquiv c
  have hne : K ≠ K.conjBy (t : G) := fun hh => hm (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
  have hneStar := starImages_ne H K (K.conjBy (t : G)) hKH hJH hK hJ hne
  have hjoin : Source.starImage H K ⊔ Source.starImage H (K.conjBy (t : G)) =
      Source.starImage H (conjugateSpanBy K T) := by
    rw [hspan, starImage_sup H K _ hKH hJH]
  obtain ⟨e₀, he₀⟩ := exists_star_product_coordinates H K (K.conjBy (t : G))
    hKH hJH hK hJ hne hq hqJ hmodel
  let e := e₀.trans (MulEquiv.subgroupCongr (congrArg (Source.starImage H) hspan.symm))
  have he : ∀ a b, (e (a, b) : Source.Hstar H) = (a : Source.Hstar H) * b := he₀
  let ee := (MulEquiv.prodCongr (MulEquiv.refl _) c).trans e
  obtain ⟨hfaith, hactor⟩ := source_section_actor_comparison H V₃ V₁ σ hσ K L₁ T
    hH hL hK hq hT hmodel ee hLN hline hseed W hW hmax hff
  have hfull := source_moved_eq_top H V₃ V₁ σ hσ K L₁ T hH hL hLN hline hseed
  let : W.quotientRepresentation.IsIrreducible :=
    maximal_component_section_irreducible σ W _ hfull hW hmax
  let := orbit_star_normal H K L₁ T hH hL
  have hqfull := quotient_full_commutator σ W _ hfull
  have hfix := image_offender_invariants_eq_bot W.quotientRepresentation _ hqfull hactor
  obtain ⟨hyp, hc, _⟩ := source_section_classification_of_adequate H V₃ V₁ σ hσ classification hSQTK
    K L₁ T hH hL hLN hline hseed W hW hmax hff
  have hfactors := markedFactors_of_classification_of_adequate W.quotientRepresentation hyp hc hfaith hfix
    _ _ _ (F918Sections.star_isComponent H K hK hq)
    (F918Sections.star_isComponent H _ hJ hqJ) hneStar hjoin e he hqfull hactor hn
    hmodel (hmodel.of_mulEquiv c.symm)
  refine ⟨e, he, hfactors, ?_, ?_⟩
  · apply moving_operator_exchanges
    have ht2 := (normalizer (K.subgroupOf H : Set H)).sq_mem_of_index_two hi t
    rw [← subgroupOf_normalizer_eq hKH] at ht2
    change (t : G) ^ 2 ∈ normalizer (K : Set G) at ht2
    rw [pow_two] at ht2
    have heq : (K.conjBy (t : G)).conjBy (t : G) = K := by
      rw [← conjBy_mul]
      exact mem_normalizer_iff_map_conj_eq.mp ht2
    rw [starImage_conjBy H _ hJH t.property, heq]
  · exact moving_operator_exchanges W.quotientRepresentation _ _ _
      (starImage_conjBy H K hKH t.property)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
