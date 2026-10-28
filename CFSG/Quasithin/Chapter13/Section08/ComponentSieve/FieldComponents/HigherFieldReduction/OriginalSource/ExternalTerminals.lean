module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.ExternalParabolic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.LinearTwoLayers

/-!
# Original external natural-layer and realized-FF exclusions

Borel centralization, the literal quotient kernel and nontrivial component
exclude a natural PSL₂ layer and one or two independently oriented odd PSL₃
layers. In the PSL₂ case the corrected native B.4.2 recognition gives either
that natural layer or a marked-five constituent. The actual multiplicity
coordinates and earlier Fitting alternatives reconstruct a faithful action
on the moved space, where the original critical geometry gives a contradiction.

The final application retains every original marking in the Borel dichotomy
and excludes both terminal module forms in its external branch. The genuine
F.9.18 FF realization remains an explicit premise of the PSL₂ exclusion.
Its construction, the exceptional outer branch, the other external fields
and final assembly remain with qt-d-138-fields-source; qt-d-1381-source
supplies the original context. Neither the legacy universal B.4.2 claim nor
an equality of the moved space with the whole module is used.
Source: Aschbacher–Smith, 13.8.20(a), printed pp.954–955.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExternalModules ExternalModules.FFSections
open Components.Swapped.LinearTwo Structure.MarkedBorel
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K X : Subgroup G}

/-- Once the original Borel centralizes V, neither natural family can occur
on its literal quotient action. The one- and two-layer ternary cases retain
independent natural/dual orientations. -/
theorem source_external_natural_false
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (hKH : K ≤ H) (B₀ : Subgroup (Source.Hstar H))
    (hB₀ : B₀ ≤ Source.starImage H K)
    (hcentral : borelResidual (borelLift H K hKH B₀) ≤ centralizer (V : Set G))
    (s : InvertedCubicTensor.S₃ →* Source.Hstar H)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (hnat : LinearTwoSections act.representation (Source.starImage H K) B₀ ∨
      LinearThreeSections act.representation (Source.starImage H K) s hs B₀) : False := by
  have hF9 := c.f9 H c.component.local_overgroup
  have hn := (normal_subgroupOf_iff_le_normalizer hKH).mp c.component.normal
  have hz := hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hk := (OddReduction.source_kernel hF9).symm
  have hqs := (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
    c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
    c.component.component).2
  let : IsQuasisimple (Source.starImage H K) := hqs
  let : IsSimpleGroup (Source.starImage H K ⧸ center (Source.starImage H K)) := hqs.simple
  let : Nontrivial (Source.starImage H K) := (QuotientGroup.mk'_surjective (center (Source.starImage H K))).nontrivial
  have hne : Source.starImage H K ≠ ⊥ := by
    intro he
    obtain ⟨k,hk⟩ := exists_ne (1 : Source.starImage H K)
    exact hk (Subtype.ext (mem_bot.mp (he ▸ k.property)))
  rcases hnat with ⟨F,hnF,e,hm,C,W,hC,hW,⟨layer⟩⟩ |
    ⟨F,hnF,ho,e,hm,C,W,hC,hσ,⟨layer⟩,htail⟩
  · exact SourceCalculation.sl2_natural_impossible H K V V₃ V₁ hKH hF9.plus_le_H
      c.localSetup.seed_le hn hz hk hne act.representation act.conjugation B₀ hB₀
      hnF F.card_eq e hm hcentral C.toSubmodule W.toSubmodule hC hW layer
  · rcases htail with hW | ⟨D,hτ,⟨second⟩,hD⟩
    · exact SourceCalculation.psl3_odd_one_layer_impossible H K V V₃ V₁ hKH hF9.plus_le_H
        c.localSetup.seed_le hn hz hk hne act.representation act.conjugation B₀ hB₀
        hnF ho F.card_eq e hm hcentral _ hσ C.toSubmodule W.toSubmodule hC hW layer
    · exact SourceCalculation.psl3_odd_two_layers_impossible H K V V₃ V₁ hKH hF9.plus_le_H
        c.localSetup.seed_le hn hz hk hne act.representation act.conjugation B₀ hB₀
        hnF ho F.card_eq e hm hcentral _ hσ _ hτ C.toSubmodule W.toSubmodule D.toSubmodule
        hC hD layer second

private theorem source_fitting_alternative
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    SolvableExclusion.ResidualAlternative L (one L T V₁) (plus L T V₁)
      (Components.Fitting.twoFittingResidual H) := by
  have h := LocalFitting.whole_residual c.localSetup c.component.local_overgroup c.earlier1339
    (SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339)
  rcases h with h | h | ⟨hm,he⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨⟨local_quotient_quasisimple c.localSetup,hm.2⟩,he⟩)

open InvertedCubicTensor
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- Native B.4.2, the original Borel centralization and the source critical
geometry exclude a realized faithful FF constituent in the external PSL₂
branch. Construction of that actual constituent remains with this task. -/
theorem source_external_linearTwo_realization_false
    [IsElementaryAbelian 2 (Source.UH H V₃)] [(Source.starImage H K).Normal]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (ha : ExternalXAlternative H K X) (hx : ExternalSourceData H K X)
    (hseed : V₃ = ⁅V₃,X⁆)
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ X = plus L T V₁))
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H)
    (hcentral : LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ centralizer (V : Set G))
    (s : S₃ →* Source.Hstar H)
    (hcomm : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    {E N : Type u} [Group E] [Finite E] [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    (σ : Representation (ZMod 2) E N)
    (hσ : B4Hypotheses KnownSimple.IsKnownSimple σ) (hff : IsFFModule σ)
    (r : LinearTwo.FiveReconstruction.ConstituentRealization act.representation
      (Source.starImage H K) σ (generalizedFitting E))
    (W : Subrepresentation act.representation)
    (hne : r.space ≠ r.space.map (act.representation (s cubic)))
    (horbit : W.toSubmodule = r.space ⊔ r.space.map (act.representation (s cubic)))
    (a : SectionMultiplicity act.representation s
      (LinearTwo.centralBottom act.representation (Source.starImage H K) W) W ≃ₗ[ZMod 2] N)
    (ha' : ∀ k v, a (sectionMultiplicityAction act.representation (Source.starImage H K).subtype
      s hcomm (LinearTwo.centralBottom act.representation (Source.starImage H K) W) W k v) =
        σ (r.component k) (a v))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2^n)) : False := by
  let : (K.subgroupOf H).Normal := c.component.normal
  let S := LocalBorel.sourceSylow H K (T : Subgroup G) hT
  let B₀ := LocalBorel.borelStar H K (T : Subgroup G) hT
  have hB : B₀.subgroupOf (Source.starImage H K) = normalizer (S : Set (Source.starImage H K)) :=
    comap_map_eq_self_of_injective (Source.starImage H K).subtype_injective _
  have hW : W.toSubmodule = orbitSpan act.representation ⊤ r.space := by
    apply le_antisymm
    · rw [horbit]
      exact sup_le (le_orbitSpan _ _ _)
        (le_iSup (fun g : (⊤ : Subgroup (Source.Hstar H)) => r.space.map (act.representation g))
          ⟨s cubic,mem_top _⟩)
    · apply orbitSpan_le _ (by rw [horbit]; exact le_sup_left)
      apply le_subspaceStabilizer
      intro g _ v hv
      exact W.apply_mem_toSubmodule g hv
  have hcases := source_external_linearTwo_layer_or_five c act X ha hx hseed s hcomm hmark
    r.space r.irrPlus W hW σ hσ hff r.component a ha' hn hm S B₀ hB
  rcases hcases with ⟨F,hdeg,e,hBe,hC,hQ,layer⟩ | ⟨_,⟨efive⟩⟩
  · exact source_external_natural_false c act hKH B₀ (map_subtype_le _)
      hcentral s hcomm (Or.inl ⟨F,by omega,e,hBe,
        LinearTwo.centralBottom act.representation (Source.starImage H K) W,W,hC,hQ,layer⟩)
  · let : Group.IsSolvable (one L T V₁ ⊔ (T : Subgroup G) : Subgroup G) :=
      LocalFitting.local_solvable c.localSetup
    have hlocal' : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
        (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = plus L T V₁) :=
      hlocal.imp id (fun h =>
      ⟨SourceAssembly.tripleCover_of_hex_mark h.1.some,h.2⟩)
    obtain ⟨_,_,_,_,hgen,_,_⟩ := source_external_cubic_action act X ha hx hseed
    obtain ⟨coord⟩ := LinearTwo.FiveReconstruction.source_moved_full_coordinates H K X V₃ V₁
      act.representation s hcomm W L (one L T V₁) (plus L T V₁) (T : Subgroup G)
      c.component.generated.symm hlocal' (source_fitting_alternative c)
      σ efive r a ha' hmark hgen hne horbit
    exact source_external_movedFive_false c act ha hlocal s W coord

/-- Apply both terminal contradictions to the original Borel dichotomy.
The exceptional outer branch and all original cubic and cover markings remain;
the external branch admits neither natural layers nor marked-five coordinates. -/
theorem source_borel_terminal_reduction
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    letI : (Source.starImage H K).Normal :=
      c.component.normal.map _ (QuotientGroup.mk'_surjective _)
    ∃ (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H),
      LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ M ∧
      ∃ (X : Subgroup G) (t : ((T : Subgroup G) ⊓ L : Subgroup G)),
        ((Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
          (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
            X = plus L T V₁ ∧ coreAction (zero L) ⟨t.val,L_normalizes_zero L t.property.2⟩ = 1)) ∧
        LocalBorel.CentralizingCalculation.InvertsTwoCoreQuotient X t.val ∧ V₃ = ⁅V₃,X⁆ ∧
        ((LocalBorel.SylowExternalXAlternative H K (T : Subgroup G) X ∧
          LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ centralizer (V : Set G) ∧
          ExternalSourceData H K X ∧
          (∀ (s : S₃ →* Source.Hstar H)
            (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g)),
            ¬ (LinearTwoSections act.representation (Source.starImage H K)
                (LocalBorel.borelStar H K (T : Subgroup G) hT) ∨
              LinearThreeSections act.representation (Source.starImage H K) s hs
                (LocalBorel.borelStar H K (T : Subgroup G) hT))) ∧
          (∀ (s : S₃ →* Source.Hstar H) (W : Subrepresentation act.representation),
            ¬ Nonempty (LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation
              (Source.starImage H K) s))) ∨
          ExceptionalOuterAlternative.{u,0} H K
            (QuotientGroup.mk' (pCore 2 H)
              ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩)) := by
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hKH,hT,hBM,X,t,hlocal,hinv,hseed,hcases⟩ := source_borel_structure c hfield
  refine ⟨hKH,hT,hBM,X,t,hlocal,hinv,hseed,?_⟩
  rcases hcases with ⟨ha,hcentral,hx⟩ | he
  · refine Or.inl ⟨ha,hcentral,hx,?_,?_⟩
    · intro s hs hnat
      exact source_external_natural_false c act hKH _ (map_subtype_le _)
        hcentral s hs hnat
    · intro s W ⟨coord⟩
      exact source_external_movedFive_false c act ha.1
        (hlocal.imp id (fun h => ⟨h.1,h.2.1⟩)) s W coord
  · exact Or.inr he

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
