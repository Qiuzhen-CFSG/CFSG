module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.ChiefComparison
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Symplectic.Source
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.AlternatingRows.Seven
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Suzuki
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields.Linear.Consumers

/-!
# Original chief-row exclusions with the comparison constructed

The original selected component supplies each chief action's full B.4
hypotheses and its simple-quotient comparison with K̂. Feeding those actual
maps to the marked configuration excludes A₇, Suzuki, the orthogonal
larger-field row and the natural SL₃ row. No comparison or module-classifier
premise is assumed: model equivalences are the alternatives being excluded.
Source: Aschbacher–Smith13.5.21, printed p.924.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open Section08.Source Configuration
open ChapterB.QuasisimpleSource
universe u

/-- The full natural Suzuki action on the genuine Fitting component. -/
@[expose] def SuzukiChiefAction {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) E W) (k : ℕ) : Prop :=
  Nonempty (Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ActionEquiv
    (ρ.comp (generalizedFitting E).subtype)
    (Chapter13.Section08.Components.Suzuki.natural k))

/-- The full natural linear-three action on the genuine Fitting component. -/
@[expose] def LinearThreeChiefAction {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) E W) (F : BinaryField) : Prop :=
  Nonempty (ActionEquiv (ρ.comp (generalizedFitting E).subtype) (linearNatural F 3))

private theorem no_suzuki {G : Type*} [Group G] [Finite G]
    {D : ChapterF.Section09.Setup G} {K : Subgroup G}
    (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    {E W : Type*} [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W)
    (comparison : Khat s h ≃* ((generalizedFitting E) ⧸ center (generalizedFitting E)))
    (k : ℕ) (hk : 0 < k) : ¬ SuzukiChiefAction ρ k :=
  LocalModels.DefiningFields.source_not_suzuki_of_configuration s h Y hY c ρ comparison k hk

private theorem no_linearThree {G : Type*} [Group G] [Finite G]
    {D : ChapterF.Section09.Setup G} {K : Subgroup G}
    (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W)
    (comparison : Khat s h ≃* ((generalizedFitting E) ⧸ center (generalizedFitting E)))
    (F : BinaryField) : ¬ LinearThreeChiefAction ρ F :=
  LocalModels.DefiningFields.source_not_linearThree_action s h Y hY c ρ
    (generalizedFitting E) comparison F
/-- The full natural symplectic action on the genuine Fitting component. -/
@[expose] def SymplecticChiefAction {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) E W) (F : BinaryField) : Prop :=
  Nonempty (ActionEquiv (ρ.comp (generalizedFitting E).subtype) (binarySymplectic F))

private theorem no_symplectic {G : Type*} [Group G] [Finite G]
    {D : ChapterF.Section09.Setup G} {K : Subgroup G}
    (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    {E W : Type*} [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W)
    (comparison : Khat s h ≃* ((generalizedFitting E) ⧸ center (generalizedFitting E)))
    (F : BinaryField) (hlarge : 1 < F.degree) : ¬ SymplecticChiefAction ρ F :=
  LocalModels.DefiningFields.Symplectic.source_not_symplectic_of_configuration s h Y hY c
    ρ comparison F hlarge

variable {G : Type u} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (K : Subgroup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
  (s : Selected D K) [(componentCentralizer s h).Normal]
  (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
  (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH) (hcard : Nat.card D.V = 16)
  (U N : Subrepresentation (representation D K h))
  (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
  (hirr : IsIrreducible (chiefRepresentation D K h U N))

include s hG hH hi hu hcard hn hirr

/-- The actual chief comparison uses the original source hypotheses alone. -/
theorem source_chief_comparison :
    Nonempty (Khat s h ≃*
      (generalizedFitting (actionImage (chiefRepresentation D K h U N)) ⧸
        center (generalizedFitting (actionImage (chiefRepresentation D K h U N))))) := by
  have hc := LocalGeometry.star_V_card_two h hi hu
  have hnorm := (s.normalizes_and_commutator h hc (selected_section_even s)).1
  let : (component D K).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (starImage D.H K).le_normalizer hnorm)
  exact source_chief_component_comparison D K h s U N hn
    (source_chief_hypotheses_all D K h s hG hH hi hu hcard U N hn hirr)

variable (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)

include Y hY c

/-- All A₇ chief-component rows contradict the original O₂,₃ and pair conditions. -/
theorem source_chief_not_seven :
    ¬ Nonempty (generalizedFitting (actionImage (chiefRepresentation D K h U N)) ≃*
      alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  obtain ⟨comparison⟩ := source_chief_comparison D K h s hG hH hi hu hcard U N hn hirr
  exact LocalModels.source_not_seven_chief_quotient s h _ comparison e Y hY c

/-- The actual Suzuki natural chief row contradicts the marked S₃ pairs. -/
theorem source_chief_not_suzuki (k : ℕ) (hk : 0 < k) :
    ¬ SuzukiChiefAction (imageRepresentation (chiefRepresentation D K h U N)) k := by
  obtain ⟨comparison⟩ := source_chief_comparison D K h s hG hH hi hu hcard U N hn hirr
  exact no_suzuki s h Y hY c
    (imageRepresentation (chiefRepresentation D K h U N)) comparison k hk

/-- Table B.4.5's orthogonal actor has an impossible positive even field degree. -/
theorem source_chief_not_orthogonal
    (Kfield F : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField)
    (degree : F.degree = 2 * Kfield.degree) :
    ¬ Nonempty (generalizedFitting (actionImage (chiefRepresentation D K h U N)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier) := by
  obtain ⟨comparison⟩ := source_chief_comparison D K h s hG hH hi hu hcard U N hn hirr
  exact LocalModels.DefiningFields.source_not_orthogonal_component s h Y c.proved_prefix
    c.condition_iv _ comparison Kfield F degree

/-- The genuine natural linear-three chief row contradicts the original residual mark. -/
theorem source_chief_not_linearThree (F : BinaryField) :
    ¬ LinearThreeChiefAction (imageRepresentation (chiefRepresentation D K h U N)) F := by
  obtain ⟨comparison⟩ := source_chief_comparison D K h s hG hH hi hu hcard U N hn hirr
  exact no_linearThree s h Y hY c
    (imageRepresentation (chiefRepresentation D K h U N)) comparison F
/-- The complete native involution-pair family excludes every larger symplectic field. -/
theorem source_chief_not_symplectic (F : BinaryField) (hlarge : 1 < F.degree) :
    ¬ SymplecticChiefAction (imageRepresentation (chiefRepresentation D K h U N)) F := by
  obtain ⟨comparison⟩ := source_chief_comparison D K h s hG hH hi hu hcard U N hn hirr
  exact no_symplectic s h Y hY c
    (imageRepresentation (chiefRepresentation D K h U N)) comparison F hlarge

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
