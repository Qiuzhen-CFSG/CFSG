module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.LocalSections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.NaturalEndpoints
public import Theory.Representation.RankOne.QuadraticRecognition.SourceTheorem

/-!
# Recognition of the two noncommuting critical sections

Apply corrected (5.12) to each actual L/O₂(P) action. Mutual normalization
proves quadraticity; Sylow-center generation proves the corrected hypothesis.
The two lower estimates and reciprocal centralizer indices force equality
and strictness. Only then is the SL₂ recognition conclusion used. The resulting
coordinates identify the same section and quotient maps. Marked natural-module
counting yields equal field orders and lifts the two actor images to the
literal opposite-center products with the vertex cores.

The earlier local model, faithful section and O²-fixed-space inputs remain
explicit. They do not assume SL₂ or natural coordinates. In particular, O₂(P)
is not replaced by O₂(L). `RecognitionSource` applies this proof to the actual
reduced graph and discharges the span, placement and intersection premises.

Source: DGS, *Groups and Graphs* (1985), (7.1), pp.126--127, using the
corrected (5.12), pp.113--115. This does not prove the Chapter 7 distance bound.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u v₀ v₁
variable {G : Type u} [Group G]

/-- Actual quotient isomorphisms and equivariant coordinates over fields of the same order. -/
@[expose] def EqualFieldNaturalSections
    {D₀ D₁ : Type u} [Group D₀] [Group D₁]
    {W₀ : Type v₀} {W₁ : Type v₁}
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (σ₀ : Representation (ZMod 2) D₀ W₀)
    (σ₁ : Representation (ZMod 2) D₁ W₁) : Prop :=
  ∃ (F₀ : Type u) (_ : Field F₀) (_ : Finite F₀) (_ : CharP F₀ 2)
    (F₁ : Type u) (_ : Field F₁) (_ : Finite F₁) (_ : CharP F₁ 2),
    let : Algebra (ZMod 2) F₀ := ZMod.algebra F₀ 2
    let : Algebra (ZMod 2) F₁ := ZMod.algebra F₁ 2
    ∃ (e₀ : D₀ ≃* SL(2,F₀)) (e₁ : D₁ ≃* SL(2,F₁))
      (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → F₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → F₁)),
      (∀ g w, E₀ (σ₀ g w) = Matrix.mulVec (e₀ g).val (E₀ w)) ∧
      (∀ g w, E₁ (σ₁ g w) = Matrix.mulVec (e₁ g).val (E₁ w)) ∧
      Nat.card F₀ = Nat.card F₁

/-- The noncircular two-sided recognition step, including the two literal Sylow products. -/
theorem source_sections_recognized
    (P₀ P₁ L₀ L₁ Z₀ Z₁ : Subgroup G) [Finite P₀] [Finite P₁]
    [IsElementaryAbelian 2 Z₀] [IsElementaryAbelian 2 Z₁]
    [((P₀.pCoreIn 2).subgroupOf L₀).Normal]
    [((P₁.pCoreIn 2).subgroupOf L₁).Normal]
    {W₀ : Type v₀} {W₁ : Type v₁}
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (σ₀ : Representation (ZMod 2) (L₀ ⧸ (P₀.pCoreIn 2).subgroupOf L₀) W₀)
    (σ₁ : Representation (ZMod 2) (L₁ ⧸ (P₁.pCoreIn 2).subgroupOf L₁) W₁)
    (d₀ : BinaryConjugationSection L₀ Z₀ (Stellmacher.omegaOneCenterAmbient L₀)
      (σ₀.comp (QuotientGroup.mk' ((P₀.pCoreIn 2).subgroupOf L₀))))
    (d₁ : BinaryConjugationSection L₁ Z₁ (Stellmacher.omegaOneCenterAmbient L₁)
      (σ₁.comp (QuotientGroup.mk' ((P₁.pCoreIn 2).subgroupOf L₁))))
    (M₀ : BinaryRankOneModel (L₀ ⧸ (P₀.pCoreIn 2).subgroupOf L₀))
    (M₁ : BinaryRankOneModel (L₁ ⧸ (P₁.pCoreIn 2).subgroupOf L₁))
    (hf₀ : Function.Injective σ₀) (hf₁ : Function.Injective σ₁)
    (hr₀ : fixedSpace σ₀ (pResidual 2 (L₀ ⧸ (P₀.pCoreIn 2).subgroupOf L₀)) = ⊥)
    (hr₁ : fixedSpace σ₁ (pResidual 2 (L₁ ⧸ (P₁.pCoreIn 2).subgroupOf L₁)) = ⊥)
    (hspan₀ : Z₀ = sylowCenterSpan L₀) (hspan₁ : Z₁ = sylowCenterSpan L₁)
    (hL₀ : L₀ ≤ P₀) (hL₁ : L₁ ≤ P₁)
    (h₁₀ : Z₁ ≤ L₀) (h₀₁ : Z₀ ≤ L₁)
    (hQ₀ : P₀.pCoreIn 2 ≤ L₀) (hQ₁ : P₁.pCoreIn 2 ≤ L₁)
    (hQC₀ : P₀.pCoreIn 2 ≤ centralizer (Z₀ : Set G))
    (hQC₁ : P₁.pCoreIn 2 ≤ centralizer (Z₁ : Set G))
    (hc₀ : Z₁ ⊓ centralizer (Z₀ : Set G) = Z₁ ⊓ P₀.pCoreIn 2)
    (hc₁ : Z₀ ⊓ centralizer (Z₁ : Set G) = Z₀ ⊓ P₁.pCoreIn 2)
    (hne : ⁅Z₀,Z₁⁆ ≠ ⊥) :
    EqualFieldNaturalSections σ₀ σ₁ ∧
    Stellmacher.IsSylowSubgroupIn (Z₁ ⊔ P₀.pCoreIn 2) L₀ ∧
    Stellmacher.IsSylowSubgroupIn (Z₀ ⊔ P₁.pCoreIn 2) L₁ := by
  let : Finite L₀ := Finite.of_injective (inclusion hL₀) (inclusion_injective _)
  let : Finite L₁ := Finite.of_injective (inclusion hL₁) (inclusion_injective _)
  let : Finite Z₀ := Finite.of_injective (inclusion d₀.section_le) (inclusion_injective _)
  let : Finite Z₁ := Finite.of_injective (inclusion d₁.section_le) (inclusion_injective _)
  let : Finite W₀ := Finite.of_surjective (fun z => (d₀.coordinates z).toAdd)
    (Multiplicative.toAdd.surjective.comp d₀.onto)
  let : Finite W₁ := Finite.of_surjective (fun z => (d₁.coordinates z).toAdd)
    (Multiplicative.toAdd.surjective.comp d₁.onto)
  let π₀ := QuotientGroup.mk' ((P₀.pCoreIn 2).subgroupOf L₀)
  let π₁ := QuotientGroup.mk' ((P₁.pCoreIn 2).subgroupOf L₁)
  let A₀ := (Z₁.subgroupOf L₀).map π₀
  let A₁ := (Z₀.subgroupOf L₁).map π₁
  obtain ⟨T₀,hT₀⟩ := ((IsElementaryAbelian.isPGroup 2 Z₁).comap_subtype (K := L₀)).exists_le_sylow
  obtain ⟨T₁,hT₁⟩ := ((IsElementaryAbelian.isPGroup 2 Z₀).comap_subtype (K := L₁)).exists_le_sylow
  let S₀ := T₀.mapSurjective (QuotientGroup.mk'_surjective ((P₀.pCoreIn 2).subgroupOf L₀))
  let S₁ := T₁.mapSurjective (QuotientGroup.mk'_surjective ((P₁.pCoreIn 2).subgroupOf L₁))
  have hg₀ : GeneratedByFixedSpace σ₀ S₀ :=
    sylow_span_fixedSpace_generated L₀ _ _ σ₀ π₀ d₀ T₀ hspan₀
  have hg₁ : GeneratedByFixedSpace σ₁ S₁ :=
    sylow_span_fixedSpace_generated L₁ _ _ σ₁ π₁ d₁ T₁ hspan₁
  have hq := critical_sections_quadratic L₀ L₁ Z₀ Z₁ _ _ σ₀ π₀ σ₁ π₁ d₀ d₁ h₁₀ h₀₁
  have hb₀ := binary_rank_one_bound_and_recognition M₀ σ₀ hf₀ S₀ A₀ (map_mono hT₀) hq.1 hg₀ hr₀
  have hb₁ := binary_rank_one_bound_and_recognition M₁ σ₁ hf₁ S₁ A₁ (map_mono hT₁) hq.2 hg₁ hr₁
  have hr := reciprocal_section_indices L₀ L₁ (P₀.pCoreIn 2) (P₁.pCoreIn 2) Z₀ Z₁ _ _
    σ₀ π₀ σ₁ π₁ d₀ d₁ h₁₀ h₀₁ (QuotientGroup.ker_mk' _) (QuotientGroup.ker_mk' _)
    hc₀ hc₁ hne hb₀.1 hb₁.1
  have hn₀ := hb₀.2 hr.2.2.2.2.1
  have hn₁ := hb₁.2 hr.2.2.2.2.2
  obtain ⟨F₀,iF₀,iFin₀,iChar₀,n₀,hnpos₀,hcard₀,e₀,hnat₀⟩ := hn₀
  obtain ⟨F₁,iF₁,iFin₁,iChar₁,n₁,hnpos₁,hcard₁,e₁,hnat₁⟩ := hn₁
  let : Algebra (ZMod 2) F₀ := ZMod.algebra F₀ 2
  let : Algebra (ZMod 2) F₁ := ZMod.algebra F₁ 2
  obtain ⟨E₀,he₀⟩ := hnat₀.2.2.2.2.2.2
  obtain ⟨E₁,he₁⟩ := hnat₁.2.2.2.2.2.2
  have hp₀ : IsPGroup 2 A₀ := (IsElementaryAbelian.isPGroup 2 Z₁).comap_subtype.map _
  have hp₁ : IsPGroup 2 A₁ := (IsElementaryAbelian.isPGroup 2 Z₀).comap_subtype.map _
  have ha₀ : A₀ ≠ ⊥ := quotient_actor_ne_bot L₀ _ Z₀ Z₁ h₁₀ hQC₀ hne
  have ha₁ : A₁ ≠ ⊥ := quotient_actor_ne_bot L₁ _ Z₁ Z₀ h₀₁ hQC₁ (by rwa [commutator_comm])
  obtain ⟨heq₀,hsyl₀⟩ := SL2NaturalOffenders.marked_sylow_of_fixed_quotient_le_card
    e₀ σ₀ E₀ he₀ ha₀ hp₀ hr.2.2.1.le
  obtain ⟨heq₁,hsyl₁⟩ := SL2NaturalOffenders.marked_sylow_of_fixed_quotient_le_card
    e₁ σ₁ E₁ he₁ ha₁ hp₁ hr.2.2.2.1.le
  refine ⟨⟨F₀,iF₀,iFin₀,iChar₀,F₁,iF₁,iFin₁,iChar₁,e₀,e₁,E₀,E₁,he₀,he₁,
    heq₀.symm.trans (hr.2.1.trans heq₁)⟩,?_,?_⟩
  · exact quotient_sylow_lifts_join L₀ _ Z₁ hQ₀ h₁₀ (isPGroup_pCoreIn 2 P₀) hsyl₀
  · exact quotient_sylow_lifts_join L₁ _ Z₀ hQ₁ h₀₁ (isPGroup_pCoreIn 2 P₁) hsyl₁

/-- Reorienting the critical pair exchanges the actual markings and preserves field equality. -/
theorem EqualFieldNaturalSections.symm
    {D₀ D₁ : Type u} [Group D₀] [Group D₁]
    {W₀ : Type v₀} {W₁ : Type v₁}
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    [AddCommGroup W₁] [Module (ZMod 2) W₁]
    {σ₀ : Representation (ZMod 2) D₀ W₀}
    {σ₁ : Representation (ZMod 2) D₁ W₁}
    (h : EqualFieldNaturalSections σ₀ σ₁) : EqualFieldNaturalSections σ₁ σ₀ := by
  obtain ⟨F₀,i₀,f₀,c₀,F₁,i₁,f₁,c₁,e₀,e₁,E₀,E₁,he₀,he₁,hcard⟩ := h
  exact ⟨F₁,i₁,f₁,c₁,F₀,i₀,f₀,c₀,e₁,e₀,E₁,E₀,he₁,he₀,hcard.symm⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
