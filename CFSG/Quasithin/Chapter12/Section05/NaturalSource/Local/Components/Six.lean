module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.SixAction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.Catalogue
public import Theory.Representation.SL5ExteriorSquare.SixDimensionalExclusion
public import Theory.Representation.SporadicSixDimensionalExclusion

/-!
# The six-space component equals the original local residual

The normalized local A₈ section restricts a containing component to L₆
itself or a two-core quotient isomorphic to SL₅(2), M₂₄ or J₄. Its literal
conjugation on V₆ is irreducible and kills the normal two-core. The actual
six-dimensional exclusions eliminate all three larger quotient models,
so K₆ = L₆. Applying this to the unique normal containing component proves
that L₆ is a C-component normal relative to G₆.

All quotient equivalences retain the original local actor. The J₄
exclusion uses inherited quasisimplicity and its certified element of
order 37; it requires no separate model simplicity assumption.
Source: Aschbacher--Smith, final paragraph of 12.5.3, printed p.819.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Representation.SL5ExteriorSquare
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The original normalized local A₈ section leaves exactly the three large models. -/
theorem local_six_component_alternatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 6))
    (hLK : s.marking.Li 6 ≤ K) :
    s.marking.Li 6 = K ∨ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) := by
  let H := s.marking.Gi 6
  let B := (s.marking.Li 6).subgroupOf H
  let C := K.subgroupOf H
  have hT := s.sylow_le_Gi 6 (Or.inr (Or.inr (Or.inr rfl)))
  let S := T.subtype hT
  have hB : B ∈ Chapter1.L H S := by
    simpa only [S, B, H, Sylow.coe_subtype] using
      (Chapter1.mem_LIn_iff_subgroupOf hT (s.marking.Li_le_Gi 6)).mp
        ⟨s.marking.Li_le_Gi 6, s.Li_mem_local 6 (Or.inr (Or.inr (Or.inr rfl)))⟩
  have hn : (S : Subgroup H) ≤ normalizer (B : Set H) := by
    intro t ht b
    exact s.sylow_normalizes_Li 6 (Or.inr (Or.inr (Or.inr rfl))) ht (b : G)
  let eB : B ≃* s.marking.Li 6 := subgroupOfEquivOfLe (s.marking.Li_le_Gi 6)
  have hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2 := by
    refine ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ⟨?_⟩⟩
    exact ((QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans
      (s.marking.LiCoreEquiv 6 (Or.inr (Or.inr (Or.inr rfl))))).trans
        Atlas.Order20160A8.sl4TwoEquivPSL
  let eC : C ≃* K := subgroupOfEquivOfLe hK.1
  let e := QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)
  rcases ChapterA.Section03.SourceEmbeddings.AlternatingEight.restricted_containing_models
      (h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 6 (Or.inr (Or.inr (Or.inr rfl)))))
      S hB.1 hK.2 (comap_mono hLK) hn hm with he | hm | hm | hm
  · left
    exact (map_subgroupOf_eq_of_le (s.marking.Li_le_Gi 6)).symm.trans
      ((congrArg (map H.subtype) he).trans (map_subgroupOf_eq_of_le hK.1))
  · exact Or.inr (Or.inl (hm.of_mulEquiv e.symm))
  · exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans hm.some⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e.symm.trans hm.some⟩))

private def linearFiveEquiv {A : Type*} [Group A] (h : ClassicalGroup.IsPSL A 5 2) :
    A ≃* Representation.SL5TenDimensional.Group := Classical.choice (by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  exact ⟨(e.trans (Atlas.fieldEquivPSL 5 (FiniteField.ringEquivOfCardEq hc))).trans
    Representation.SL5TenDimensional.projectiveEquiv.symm⟩)

/-- The actual six-space action excludes all strict containing components. -/
theorem local_six_component_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 6))
    (hLK : s.marking.Li 6 ≤ K) : s.marking.Li 6 = K := by
  let ρ := s.marking.sixAction.comp (inclusion hK.1)
  have hk : pCore 2 K ≤ ρ.ker := s.marking.sixAction_twoCore_le_ker hK.1 hLK
  let σ := Representation.quotientOfLEKer ρ (pCore 2 K) hk
  let : Representation.IsIrreducible ρ := s.marking.sixAction_overgroup_irreducible hK.1 hLK
  let : Representation.IsIrreducible σ :=
    (Representation.quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance
  have hd : Module.finrank (ZMod 2) V₆ = 6 := standard_dimensions.2.2.2.1
  rcases s.local_six_component_alternatives h hK hLK with he | hm | hm | hm
  · exact he
  · let e := linearFiveEquiv hm
    let τ := σ.comp e.symm.toMonoidHom
    let : Representation.IsIrreducible τ :=
      (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective σ).mpr inferInstance
    exact (Representation.SL5TenDimensional.Classification.no_irreducible_six τ hd).elim
  · let e := hm.some
    let τ := σ.comp e.symm.toMonoidHom
    let : Representation.IsIrreducible τ :=
      (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective σ).mpr inferInstance
    exact (Representation.no_irreducible_mathieu_six τ hd).elim
  · let e := hm.some
    let : IsQuasisimple (K ⧸ pCore 2 K) :=
      s.local_linear_four_component_quasisimple h 6 (Or.inr rfl) hK hLK
    let : IsQuasisimple Janko4.Model := IsQuasisimple.of_mulEquiv e
    let τ := σ.comp e.symm.toMonoidHom
    let : Representation.IsIrreducible τ :=
      (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective σ).mpr inferInstance
    exact (Representation.no_irreducible_janko_six τ hd).elim

/-- The i = 6 component and relative normality conclusion of source 12.5.3. -/
theorem local_six_component_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    s.marking.Li 6 ∈ Chapter1.cComponentsIn (s.marking.Gi 6) ∧
      ((s.marking.Li 6).subgroupOf (s.marking.Gi 6)).Normal := by
  obtain ⟨K, ⟨hK, hLK, hn⟩, _⟩ := s.exists_unique_normal_local_component h 6
    (Or.inr (Or.inr (Or.inr rfl)))
  exact (s.local_six_component_eq h hK hLK).symm ▸ ⟨hK, hn⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
