module
public import Theory.SpecificGroups.PSL3.SquareFieldComponentNormal
public import Theory.GroupTheory.CComponent.ContainedGeneralizedFitting
public import Theory.GroupTheory.GeneralizedFitting.PreimageMovement
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ContainedComponentPromotion
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalization
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels

/-!
# Escaping components in the Hermitian pushing-up configuration

Containment of the generalized Fitting preimage makes the original perfect
residual an ambient C-component. Its actual square-field PSL₃ marking then
forces normality in H, contradicting the proper normalizer of its span.
Thus C.2.11 selects an escaping component on the same source subgroups.
Ordinary components retain the original residual and full module; constrained
components retain their literal C.2.7 input and actual star-image model.

This is a component selection, not an exclusion of the selected alternatives.
The remaining alternatives and the field-four branch are retained by
qt-d-1222-nonmathieu-hermitian-exclusion.
Source: Aschbacher--Smith C.2.11--13, C.3.2--4, C.4.4--8, pp.148--154,
applied in 4.4.6, p.620 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian

/-- The original square-field quotient excludes the contained-Fitting branch. -/
theorem pushingUp_fitting_escape {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) [IsQuasisimple (B ⧸ pCore 2 B)]
    {n : ℕ} (hn : 1 < n) (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E)) :
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H := by
  intro hf
  have hBH := h.component_le.trans h.local_le
  let A := B.subgroupOf H
  let N := M.subgroupOf H
  let eB : A ≃* B := subgroupOfEquivOfLe hBH
  let eqB : (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eqB.symm
  let ez : ((A ⧸ pCore 2 A) ⧸ center (A ⧸ pCore 2 A)) ≃* PSL(3,E) :=
    (QuotientGroup.congr _ _ eqB (FixedElementary.map_center eqB)).trans e
  have hN : M ≤ normalizer (B : Set G) := h.normalizes_of_fitting_contained hstrict hf
  have hs : conjugateSpanBy B M = B := h.span_eq_of_fitting_contained hstrict hf
  let : Group.IsPerfect B := hs ▸ h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := eB.symm.toMonoidHom) eB.symm.surjective
  have hNA : N ≤ normalizer (A : Set H) := by
    rw [←subgroupOf_normalizer_eq hBH]
    exact comap_mono hN
  have hAN : A ≤ N := comap_mono h.component_le
  have hQ : pCore 2 H ≤ N := by
    apply le_trans ?_ hf
    simpa only [QuotientGroup.ker_mk'] using
      MonoidHom.ker_le_comap (QuotientGroup.mk' (pCore 2 H)) (generalizedFitting (H ⧸ pCore 2 H))
  have hcore : A.pCoreIn 2 ≤ pCore 2 H :=
    (pCoreIn_mono_of_normalizes hAN hNA).trans (pCoreIn_le_of_generalizedFitting_preimage_le N hf)
  have hU : (⁅pCore 2 A,(⊤ : Subgroup A)⁆).map A.subtype ≤ pCore 2 H :=
    (map_mono (commutator_le_left _ _)).trans hcore
  have hA : A.IsCComponent :=
    isCComponent_of_contained_generalizedFitting A N hAN hNA hQ hU hf
  let : A.Normal := Matrix.PSL3.cComponent_normal_of_square_field_quotient h.sqtk.stronglyQuasithin hn hc A hA ez
  have hHN : H ≤ normalizer (B : Set G) := by
    have hh := A.le_normalizer_map H.subtype
    simpa only [A,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hBH] using hh
  have hHM : H ≤ M := by
    rw [← h.normalizer_span_eq, hs]
    exact le_inf le_rfl hHN
  exact hstrict.not_ge hHM

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- The actual square-field source pair has an escaping ordinary or constrained component. -/
theorem pushingUp_escaping_component
    {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
    {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) [IsQuasisimple (B ⧸ pCore 2 B)]
    {n : ℕ} (hn : 1 < n) (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E)) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H ∧
      conjugateSpanBy B M ≤ normalizer (K.map H.subtype : Set G) ∧
      ((IsComponent H K ∧ K.Normal ∧ B.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K) ∨
        (generalizedFitting K = pCore 2 K ∧
          Input KnownSimple.IsKnownSimple H R M (K.map H.subtype) ∧
          ChapterC.C27Source.StarModels.Model
            (starImage (K.map H.subtype) R (K.map H.subtype)))) := by
  obtain ⟨K,hK,hq,hout,hnorm,hcases⟩ :=
    h.ordinary_or_constrained_escape (pushingUp_fitting_escape h hstrict hn hc e)
  refine ⟨K,hK,hq,hout,hnorm,?_⟩
  rcases hcases with ho | hfK
  · exact Or.inl ⟨ho,h.ordinary_component_normal K ho,
      h.ordinary_component_contains_original K ho,
      (h.ordinary_module_placement K ho).1.trans inf_le_right⟩
  · exact Or.inr ⟨hfK,h.constrained_source_input K hK hq hout hfK,
      ChapterC.C27Source.star_model_from_source
        (h.constrained_source_input K hK hq hout hfK)⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
