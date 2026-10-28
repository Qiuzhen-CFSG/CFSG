module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.FixedSpace
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.Seed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.AlternatingNatural
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.SmallModules.Consumers
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.LocalData
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OddReduction
public import Theory.SpecificGroups.Alternating.SevenComponent.Normality
/-!
# Original-family exclusion of the alternating group of degree seven

Start with the original natural A₆ local setup. The preceding F.9,
13.8.13 and 13.8.21 hypotheses construct the canonical binary conjugation
action and a selected critical pair. The compatible four/six/four-plus-dual
classification, faithful seven-point results, source seed, marked covered
residuals and full fixed-space displacement construct every Earlier field.
The existing proof then closes both actual partition branches.

For an arbitrary original family member, its strongly quasithin local
rank makes the A₇ component normal relative to that member. The literal
13.8.16 reduction retains its intrinsic quotient and transports its
component assertion. Applying the reduced exclusion gives the uniform
source assertion. The final theorem applies this exclusion directly to
the 13.8.25 binary group-reduction consumer.

This completes the conditional contract of qt-d-138-linear-seven-source.
The genuine preceding recognition, geometry, solvable-overgroup and
component inputs remain explicit; qt-d-138-linear-source owns their final
discharge, with qt-d-138-geometry-source and qt-d-138-fields-source supplying
their corresponding source results. No small-module, Clifford, extension,
critical-pair, rank, local-residual, displacement or LocalData callback
remains as a premise. No ambient normality is asserted for the component.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
13.8.24, printed pp.958–959/PDF pp.975–976, and its application in
13.8.25, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open SourceCompletion CriticalGeometry TransvectionRecognition.Component.ModelExtension
open PairsBranch PairsBranch.ModuleSelection FourThreeBranch.NaturalSelection
open Chapter1.Section02.LocalModels Chapter2.ComponentRefinement.LieType.Binary
open FieldComponents.HigherFieldReduction.ExternalModules
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
section
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
theorem source_earlier
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : TransvectionRecognition.Solvable.EarlierLocalInputs (G := G))
    (hG64 : TransvectionRecognition.Component.RecognitionStep.G64SourceTheorem.{u}
      KnownSimple.IsKnownSimple)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal) (hKT : K ⊔ (T : Subgroup G) = H)
    (hLK : sourceOne L T V₁ ≤ K)
    (htheta : sourceOne L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : PairsBranch.CentralAction.IsSourceAction H V₃ V₁ ρ)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    ∃ c : CriticalPair L (T : Subgroup G) H V,
      SourceExclusion.Earlier c K (sourceOne L T V₁) (zero L) (plus L T V₁) G₁ M V₃ V₁ ρ := by
  let := vh_elementary d hH
  let := LocalFitting.local_solvable d
  obtain ⟨c, hs, hr, hVr⟩ := source_selected_geometry d earlier localEarlier hG64 hH hF9
    hcentral hcomm hKH hK hN hKT e htheta h13 (source_covered_nine d) ρ hρ
  let s := CriticalInputs.sourceSection H V₃ V₁ ρ hρ hF9.plus_le_H
    (d.line_le_plane.trans d.plane_le_seed) hF9.H_centralizes
  refine ⟨c, {
    member := hH
    component_le := hKH
    component := hK
    component_normal := hN
    supplement := hKT
    local_le_component := hLK
    base_solvable := inferInstance
    sylow := source_sylow hH
    two_group := T.isPGroup'
    theta := htheta
    solvable_overgroups := h13
    flag := d.seed_le
    line_le := d.line_le_uh H
    source_action := hρ
    transvection_models := fun a _ hc =>
      AlternatingAndLinear.TransvectionSource.transvection_models d earlier localEarlier hG64 hH ρ hρ a hc
    covered_nine := source_covered_nine d
    edge := hr.edge
    terminal_core := hr.terminal_core
    Vgamma_le := hr.Vgamma_le
    Vgamma_placement := hs.2.2.2.2.2.2.2
    alternatives := Or.inr (Or.inr hs)
    reciprocal_inputs := fun _ => hr
    Vgamma_quadratic := (c.quadratic_star_on_Utilde V₃ V₁ s d.seed_le
      (local_earlierGeometry d hF9 c).VH_endpoint).1
    local_models := by
      rcases local_quotient_alternatives d with ⟨a, _⟩ | ⟨a, _⟩
      · exact Or.inl ⟨a⟩
      · exact Or.inr ⟨a⟩
    six_local_card := LocalFitting.ordinary_core_card d
    covered_local_rank := source_covered_local_rank d
    covered_residuals := source_covered_residual_data d
    generated := source_generated_original d hKH hN hLK
    monolith := (source_structure hH hKH hK hN hKT e).2.2
    seed_nontrivial := seed_nontrivial d
    seed_commutator := Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup d)
    seed_normalized := source_seed_normalized d
    seed_irreducible := source_seed_irreducible_original d hH ρ hρ
    seed_rank := source_seed_rank d
    seed_centralized := source_zero_centralizes_seed d
    small_modules := fun φ hi hKφ => source_small_quadratic φ hi _ hKφ
    alternating_natural := alternating_natural d earlier ρ
    no_strong := sevenPointNoStrongInput
    recognition := sevenPointRecognitionInput
    strict_centralizer := by
      intro W hW hRank hKW
      have hKQ := nontrivial_on_quotient_of_generated ρ W (Source.starImage H K) hW.1
        (source_linear_generated_original d hKH hN hLK ρ hρ)
      exact (source_no_rank_one_configuration_from_geometry d hH hF9 K hKH hK hN hKT e ρ hρ
        W c hKW hKQ hRank hs.2.2.2.1 hVr).elim }⟩

end
section
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
/-- All consumed local data, with the canonical conjugation action on U_H/V₁. -/
theorem source_local_data
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : TransvectionRecognition.Solvable.EarlierLocalInputs (G := G))
    (hG64 : TransvectionRecognition.Component.RecognitionStep.G64SourceTheorem.{u}
      KnownSimple.IsKnownSimple)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal) (hKT : K ⊔ (T : Subgroup G) = H)
    (hLK : sourceOne L T V₁ ≤ K)
    (htheta : sourceOne L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    Nonempty (SourceExclusion.LocalData L T H V K (sourceOne L T V₁)
      (zero L) (plus L T V₁) G₁ M V₃ V₁) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hH
  let : (V₁.subgroupOf (Source.UH H V₃)).Normal := inferInstance
  let a := Comparison.conjugationAction (d.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hF9.commutator_UH_QH_le_point
  obtain ⟨c, hc⟩ := source_earlier d earlier localEarlier hG64 hH hF9 hcentral hcomm
    hKH hK hN hKT hLK htheta h13 a.representation a.conjugation e
  exact ⟨{
    elementary_U := inferInstance
    elementary_V := vh_elementary d hH
    denominator_normal := inferInstance
    pair := c
    representation := a.representation
    earlier := hc }⟩

/-- The complete reduced seven-point exclusion, retaining only preceding
source hypotheses. Every module and critical-geometry callback is discharged. -/
theorem not_alternatingSeven_reduced
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : TransvectionRecognition.Solvable.EarlierLocalInputs (G := G))
    (hG64 : TransvectionRecognition.Component.RecognitionStep.G64SourceTheorem.{u}
      KnownSimple.IsKnownSimple)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal) (hKT : K ⊔ (T : Subgroup G) = H)
    (hLK : sourceOne L T V₁ ≤ K)
    (htheta : sourceOne L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  obtain ⟨a⟩ := source_local_data d earlier localEarlier hG64 hH hF9 hcentral hcomm
    hKH hK hN hKT hLK htheta h13 e
  exact a.not_alternatingSeven ⟨e⟩
end

section
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
/-- Original 13.8.24, uniformly in the actual local family. The preceding
F.9 and 13.8.13,16,21 conclusions remain explicit for the parent source
assembly; all seven-point representation and critical-pair inputs are proved. -/
theorem not_alternatingSeven_original
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : TransvectionRecognition.Solvable.EarlierLocalInputs (G := G))
    (hG64 : TransvectionRecognition.Component.RecognitionStep.G64SourceTheorem.{u}
      KnownSimple.IsKnownSimple)
    (hF9 : ∀ J ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (htheta : ∀ J ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      sourceOne L T V₁ = closure {x : G | x ∈ J ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (h16 : ∀ J C : Subgroup G, J ∈ Source.Hz (sourceOne L T V₁) T G₁ M →
      C ≤ J → (C.subgroupOf J).IsCComponent → (C.subgroupOf J).Normal →
      C ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (h21 : ∀ J C : Subgroup G, J ∈ Source.Hz (sourceOne L T V₁) T G₁ M →
      C ≤ J → (C.subgroupOf J).IsCComponent → (C.subgroupOf J).Normal →
      J = C ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) →
      C ⊔ (T : Subgroup G) = J ∧ sourceOne L T V₁ ≤ C)
    {H K : Subgroup G} (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    ¬ IsAlternating (K ⧸ pCore 2 K) 7 := by
  rintro ⟨e⟩
  let eK := (QuotientGroup.congr (pCore 2 (K.subgroupOf H)) (pCore 2 K)
    (subgroupOfEquivOfLe hKH) (pCore_map_iso 2 _)).trans e
  have hn := alternatingGroup.SevenComponent.normal_of_core_quotient hK eK
    (OddReduction.local_stronglyQuasithin d hH.2.1 3 Nat.prime_three (by decide))
  apply LocalGeometry.exclude_original_of_reduced (sourceOne L T V₁) (T : Subgroup G) G₁ M
    H K hH hKH hK hn (h16 H K hH hKH hK hn) e
  intro J hJ hKJ hc hnJ he hA7
  obtain ⟨hJT, hLJ⟩ := h21 J K hJ hKJ hc hnJ he
  exact not_alternatingSeven_reduced d earlier localEarlier hG64 hJ (hF9 J hJ)
    hcentral hcomm hKJ hc hnJ hJT hLJ (htheta J hJ) h13 hA7
end

section
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
open AlternatingAndLinear.LinearReduction
/-- The actual 13.8.25 group consumer, with its uniform A₇ exclusion
constructed. Remaining group/module premises belong to qt-d-138-linear-source. -/
theorem source_linear_reduction
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : TransvectionRecognition.Solvable.EarlierLocalInputs (G := G))
    (hG64 : TransvectionRecognition.Component.RecognitionStep.G64SourceTheorem.{u}
      KnownSimple.IsKnownSimple)
    (hF9 : ∀ J ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (groups : SourceReduction.GroupFacts L (sourceOne L T V₁) (T : Subgroup G) V V₁ V₃ G₁ M)
    (modules : ∀ J C : Subgroup G, J ∈ Source.Hz (sourceOne L T V₁) T G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent →
      Nonempty (SourceReduction.LocalModuleData L T J V C (sourceOne L T V₁) G₁ M V₃ V₁))
    {𝒦 : GroupClass.{u}} (embeddings : Overgroup.EarlierEmbeddings 𝒦)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁))
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) :
    n = 4 ∧ IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      Nonempty (Source.Hstar H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) ∧ H = G₁ := by
  have hline : V₁ ≠ ⊥ := by
    intro he
    have hh := d.line_card
    rw [he, card_bot] at hh
    omega
  have hp : IsPGroup 2 V₁ := isPGroup_iff_card_dvd_pow.mpr
    ⟨1, by rw [d.line_card]; norm_num⟩
  have hVT : V₁ ≤ (T : Subgroup G) := hp.le_sylow_of_normalized T d.line_stable
  apply SourceReduction.source_linear_reduction L (sourceOne L T V₁) V V₁ V₃ G₁ M T groups
    modules embeddings hQ ?_ hline hp (hVT.trans le_sup_right) d.first_normalizer.le
    hH hKH hK hn₀ hn₁ hmodel
  intro J C hJ hCJ hC
  exact not_alternatingSeven_reduced d earlier localEarlier hG64 hJ (hF9 J hJ) hcentral hcomm
    hCJ hC (groups.component_normal hJ hCJ hC) (groups.supplement hJ hCJ hC).symm
    (groups.base_le_component hJ hCJ hC) (groups.theta J hJ) groups.solvable_overgroups
end
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
