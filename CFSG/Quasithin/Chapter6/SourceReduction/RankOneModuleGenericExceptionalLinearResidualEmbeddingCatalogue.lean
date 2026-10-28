module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.ContainingModels
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingJankoTwo

/-!
# Remaining containing models for the exceptional residual

The actual unique normal containing C-component is compared with the proved
exceptional catalogue. The Mathieu graph exclusion removes its M₂₃ row. The Hall–Janko section
exclusion then removes J₂, leaving only the exact J₄ quotient carrier for
a proper containing component. This remaining row is an explicit mathematical
obligation; maximality is not asserted here.

Source: Aschbacher–Smith A.3.12, 5.1.12 and 5.1.14, printed pp.47–48,
635 and 638 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric

/-- After excluding the actual M23 graph action, the proved containing catalogue
leaves equality or the two Janko rows. These rows are not asserted to occur. -/
theorem linear_four_containing_component_eq_or_janko
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {K Y : Subgroup G} (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hg : HasLinearFourGraphAction (T : Subgroup G) K)
    (hY : Y ∈ Chapter1.HOver G (T : Set G)) (C : Subgroup Y)
    (hC : C.IsCComponent) (hnC : C.Normal) (hKC : K ≤ C.map Y.subtype) :
    K = C.map Y.subtype ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) := by
  let : C.Normal := hnC
  have hKY : K ≤ Y := hKC.trans (map_subtype_le C)
  let S := T.subtype hY.2
  let B := K.subgroupOf Y
  have hB : B ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hY.2 hKY).mp ⟨hKY,hK⟩
  have hnB : (S : Subgroup Y) ≤ normalizer (B : Set Y) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro k
    exact mem_normalizer_iff.mp (hn ht) (k : G)
  have hBC : B ≤ C := by
    intro k hk
    obtain ⟨c,hc,he⟩ := hKC hk
    exact Y.subtype_injective he ▸ hc
  have hmodel : ChapterA.Section03.SourceEmbeddings.Exceptional.IsModel
      (B ⧸ pCore 2 B) := by
    obtain ⟨F,hF,hfin,hcard,e,_⟩ := hg.subgroupOf hY.2 hKY
    let : Fintype F := Fintype.ofFinite F
    let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
    let a : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard,
        Matrix.PSL3Four.card_F])
    exact Or.inr (Or.inr ⟨e.trans (Atlas.fieldEquivPSL 3 a)⟩)
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk hG hY.1
  obtain ⟨C',hC',hnC',hBC',hm⟩ :=
    ChapterA.Section03.SourceEmbeddings.Exceptional.exists_normal_containing_models
      hQ S hB hnB hmodel
  obtain ⟨A,_,hu⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ S hB hnB
  have he : C' = C :=
    (hu C' ⟨hC',hBC',hnC'⟩).trans (hu C ⟨hC,hBC,hnC⟩).symm
  rw [he] at hm
  rcases hm with heq | hJ2 | hM23 | hJ4
  · apply Or.inl
    have heq' := congrArg (map Y.subtype) heq
    simpa only [B,map_subgroupOf_eq_of_le hKY] using heq'
  · exact Or.inr (Or.inl hJ2)
  · exact (linear_four_graph_excludes_mathieu23_container T hY.2 hn hg C hKC hM23).elim
  · exact Or.inr (Or.inr hJ4)

/-- The remaining proper-containing cases for the literal exceptional residual.
The M23 row is discharged, and the two Janko cases remain exact quotient models. -/
theorem linear_residual_proper_containing_component_janko
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H Y : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hnC : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype) (hne : residual H ≠ C.map Y.subtype) :
    Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) :=
  (linear_four_containing_component_eq_or_janko hG T
    (linear_residual_mem_localFamily hH.1.1 hlinear)
    (hH.1.1.2.trans (le_normalizer_residual H))
    (linear_residual_graph_action T hTM hH hlinear)
    ⟨hY.1,hH.1.1.2.trans hY.2⟩ C hC hnC hRC).resolve_left hne

/-- After the Mathieu and Hall--Janko exclusions, every proper containing
component of the actual exceptional residual has precisely the J₄ quotient. -/
theorem linear_residual_proper_containing_component_jankoFour
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H Y : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hnC : C.Normal)
    (hRC : residual H ≤ C.map Y.subtype) (hne : residual H ≠ C.map Y.subtype) :
    Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) :=
  (linear_residual_proper_containing_component_janko hG T hTM hH hlinear
    hY C hC hnC hRC hne).resolve_left
    (linear_residual_excludes_jankoTwo_container hY.2 C hRC hlinear)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
