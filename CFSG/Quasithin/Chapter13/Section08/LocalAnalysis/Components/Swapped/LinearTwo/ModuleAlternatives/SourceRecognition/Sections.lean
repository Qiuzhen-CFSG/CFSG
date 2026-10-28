module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Actor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.NoStrong
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918.Faithful

/-!
# The maximal section of the original exchanged linear-two module

The field-four actor and the no-strong-module theorem exclude strong
FF-modules on both literal section images. The genuine F.9 edge actor
supplies the bounded quadratic action faithful on the component orbit.
Comparing its conjugation action with the supplied source representation
then yields the maximal-submodule FF/central dichotomy used in 13.8.16(1).
The seed has nonzero projection on the quotient; in the central branch an
actual Irr⁺ section generates the whole module under H*.

The FF cross-factor classification and the central-branch whole-module
identification remain subsequent obligations. This module does not assert
the final module alternatives or 13.8.16(1).

Source: Aschbacher–Smith, 13.8.16(1), printed p.952, using F.9.18(5–6).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open F918Sections.NoStrong
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open SolvableExclusion Three.Supercritical.Offenders

private theorem source_representation_eq
    {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (a : Five.StarAction H (Source.UH H V₃) V₁) : ρ = linearAction a := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  have hv : v = Additive.ofMul (sourceProjection H V₃ V₁ u) := hu.symm
  rw [hv,hρ]
  exact congrArg Additive.ofMul (a.conjugation x u).symm

open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving


/-- Neither literal section admits a strong offender; all field-four and
faithful-image premises are deduced from the original source inputs. -/
theorem source_section_noStrong {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) :
    (∀ W : Subrepresentation ρ, W ≠ ⊤ →
      ¬ W.toSubmodule ≤ fixedSpace ρ (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) →
      ¬ IsStrongFFModule (imageRepresentation W.toRepresentation)) ∧
    (∀ W : Subrepresentation ρ, W ≠ ⊤ →
      ¬ IsStrongFFModule (imageRepresentation W.quotientRepresentation)) := by
  obtain ⟨t,ht,htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  obtain ⟨F,hF,hfin,hchar,a,_,_,ha,_⟩ := exists_source_exchangedActor
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ht htn
  have hfull := Original.moved_eq_top d h hF9all hcentral hcomm hsource hH hKH hK
    hmoving hn hmodel hgen ρ hρ
  rw [← ha] at hfull ⊢
  exact a.section_exclusions_of_faithful_exclusion ρ
    (fun _ _ _ _ σ hf => exchanged_not_strong a σ hf) hfull

/-- The actual maximal source quotient satisfies the FF/central dichotomy.
The F.9 edge actor and B.4 no-strong hypotheses are constructed here. -/
theorem source_section_dichotomy {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [hEA : IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) :
    ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧
      (∀ Y : Subrepresentation ρ, W ≤ Y → Y ≠ ⊤ → Y = W) ∧
      (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ ≠ ⊥ ∧
      ((IsFFModule (imageRepresentation W.toRepresentation) ∧
        IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
       (subspaceCommutator ρ W.toSubmodule (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) = ⊥ ∧
        ∃ I, IsIrrPlus ρ (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) I ∧ seedSpan ρ I = ⊤)) := by
  have hL := Original.one_le_orbit d h hF9all hcentral hcomm hsource hH hKH hK hmoving hn hmodel
  have hq := (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  obtain ⟨a,B,_,_,hA,hfaith⟩ := @F918.source_component_actor G _ _ T L V V₁ V₂ V₃ M G₁ H
    d hEA h hF9all hcentral hcomm hsource hH K hKH hK hgen
  rw [← source_representation_eq H V₃ V₁ ρ hρ a] at hA
  obtain ⟨hnW,hnQ⟩ := source_section_noStrong d h hF9all hcentral hcomm hsource hH
    hKH hK hgen hmoving hn hmodel ρ hρ
  apply F918Sections.exists_source_section_dichotomy H V₃ V₁ ρ hρ K (one L T V₁) T
    hgen.symm hL hK hq
    (Section07.ModelExclusions.point_residual_normalizes_seed (localNaturalSetup d))
    (hF9all H hH).point_lt _ (Source.starImage H B) hA.1 hA.2.2 hfaith hnW hnQ
  rw [commutator_comm, Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup d)]
  exact le_sup_left

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
