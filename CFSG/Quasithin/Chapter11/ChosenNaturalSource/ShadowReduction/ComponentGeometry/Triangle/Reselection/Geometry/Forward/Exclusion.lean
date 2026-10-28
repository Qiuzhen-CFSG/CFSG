module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Forward.Plane
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Exclusion
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Source

/-!
# Excluding the original field-four triangle

The earlier source recognition constructs the swapped natural module. Its
first residual is K₀ and its second is the original L₂. The two vertices
escape each other's normalizer, so the common-plane rank contradiction
applies in either orientation, retaining the actual radicals throughout.

This proves the surviving equality, odd-extension and prime-PSL₂ list in
11.4.1(2), conditional only on the registered earlier source implications
and original component geometry. Their final discharge belongs to
qt-d-1222-shadow-components and qt-d-1222-natural-shadow-reduction.
Radical/OddIndex/CanonicalSource adds the two bounds of 11.4.1(3)
without requiring the independent Fitting-index calculation.
Source: Aschbacher–Smith, 11.4.1(2), printed pp.775–776.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
open LocalGeometry ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The forward rank contradiction now follows from the actual third
vertex and earlier source implications, with no paired-placement input. -/
theorem ofFlag_no_forward_choice
    {L V : Subgroup G} (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    (m : ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (ChapterB.QuasisimpleSource.binaryG2 S.field))
    (f : InvariantFlag (Coordinates.g2 m)) (hd : S.field.degree = 2)
    {K K₀ W : Subgroup G}
    (hK : K ≤ normalizer (f.Vi 0 : Set G))
    (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ ≤ K) (hne : K₀ ≠ f.Li 0)
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (D_J : Chapter12.Section02.ChosenModule T (K₀ ⊔ f.Li 1) W)
    (S_J : D_J.NonbinaryNaturalInput)
    (m_J : ChapterB.QuasisimpleSource.ActionEquiv D_J.centralQuotientAction
      (ChapterB.QuasisimpleSource.binarySymplectic S_J.field))
    (hd_J : S_J.field.degree = 2)
    (V₁ : Submodule (ZMod 2) D.chosenCentralQuotient)
    (W₁ : Submodule (ZMod 2) D_J.chosenCentralQuotient)
    (h1132 : ∀ H, Hypothesis1131At D S V₁ H → Proposition1132At D S V₁ H)
    (h1132_J : ∀ H, Hypothesis1131At D_J S_J W₁ H → Proposition1132At D_J S_J W₁ H)
    (hw : indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hs : @ChapterE.globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hr : (2 * S.field.degree : ℕ∞) < ChapterE.globalR V) : False := by
  have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
  have hF_J : Nat.card S_J.field.Carrier = 4 := by simpa [hd_J] using S_J.field.card_eq
  have ho : Components.TriangleOrientation L (K₀ ⊔ f.Li 1) := Or.inl
    ⟨⟨S.field.Carrier, inferInstance, inferInstance, hF, ⟨m.groupEquiv⟩⟩,
      ⟨S_J.field.Carrier, inferInstance, inferInstance, hF_J, ⟨m_J.groupEquiv⟩⟩⟩
  let f_J := Sp4.flag m_J S_J
  have hfirst := triangle_other_eq_firstResidual D_J S_J f_J rfl hK₀ hK₀K hKZ
    (fixed_trivial_of_triangle_order D_J S_J hd_J ho W₁ h1132_J)
  have hsecond := reselected_second_eq D S f hK hK₀ hK₀K hne D_J S_J hd_J ho
    f_J (Sp4.flag_inner_unique m_J S_J) hfirst
  have hout := (triangle_vertices_escape D S f hK hK₀ hK₀K hne
    S_J.source.maximal_faithful.1.1).1
  apply no_common_plane D S m f hd D_J S_J (alignedSymplecticMark S_J m_J)
    hd_J V₁ W₁ h1132 h1132_J hout hw hs hr le_sup_right
  simpa only [hsecond] using alignedSymplecticMark_plane_image S_J m_J f_J

/-- The reverse orientation uses the original symplectic module and the
literal reselected G₂ flag. Mutual escape removes any assumption that K
is already a component of the new point normalizer. -/
theorem ofFlag_no_reverse_choice
    {L V : Subgroup G} (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    (m : ChapterB.QuasisimpleSource.ActionEquiv D.centralQuotientAction
      (ChapterB.QuasisimpleSource.binarySymplectic S.field))
    (f : InvariantFlag (Coordinates.sp4 m)) (hd : S.field.degree = 2)
    {K K₀ W : Subgroup G}
    (hK : K ≤ normalizer (f.Vi 0 : Set G))
    (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ ≤ K) (hne : K₀ ≠ f.Li 0)
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (D_J : Chapter12.Section02.ChosenModule T (K₀ ⊔ f.Li 1) W)
    (S_J : D_J.NonbinaryNaturalInput)
    (m_J : ChapterB.QuasisimpleSource.ActionEquiv D_J.centralQuotientAction
      (ChapterB.QuasisimpleSource.binaryG2 S_J.field))
    (hd_J : S_J.field.degree = 2)
    (V₁ : Submodule (ZMod 2) D.chosenCentralQuotient)
    (W₁ : Submodule (ZMod 2) D_J.chosenCentralQuotient)
    (h1132 : ∀ H, Hypothesis1131At D S V₁ H → Proposition1132At D S V₁ H)
    (h1132_J : ∀ H, Hypothesis1131At D_J S_J W₁ H → Proposition1132At D_J S_J W₁ H)
    (hw : indexedWeakClosure W (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (W : Set G))
    (hs : @ChapterE.globalS G _ W D_J.elementary = (2 * S_J.field.degree : ℕ))
    (hr : (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W) : False := by
  have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
  have hF_J : Nat.card S_J.field.Carrier = 4 := by simpa [hd_J] using S_J.field.card_eq
  have ho : Components.TriangleOrientation L (K₀ ⊔ f.Li 1) := Or.inr
    ⟨⟨S.field.Carrier, inferInstance, inferInstance, hF, ⟨m.groupEquiv⟩⟩,
      ⟨S_J.field.Carrier, inferInstance, inferInstance, hF_J, ⟨m_J.groupEquiv⟩⟩⟩
  let f_J := G2.flag S_J m_J
  have hfirst := triangle_other_eq_firstResidual D_J S_J f_J rfl hK₀ hK₀K hKZ
    (fixed_trivial_of_triangle_order D_J S_J hd_J ho W₁ h1132_J)
  have hsecond := reselected_second_eq D S f hK hK₀ hK₀K hne D_J S_J hd_J ho
    f_J (G2.flag_inner_unique S_J m_J) hfirst
  have hout := (triangle_vertices_escape D S f hK hK₀ hK₀K hne
    S_J.source.maximal_faithful.1.1).2
  apply no_common_plane D_J S_J m_J f_J hd_J D S (alignedSymplecticMark S m)
    hd W₁ V₁ h1132_J h1132 hout hw hs hr
  · rw [hsecond]
    exact (localResidual_le _).trans inf_le_left
  · rw [hsecond]
    exact alignedSymplecticMark_plane_image S m f

/-- Eliminate the original field-four triangle from genuine earlier source
implications. The swapped chosen module and both paired flags are constructed;
all common-plane, action and escape premises are discharged here.
The earlier 7.0.1, 3.2.5, 11.2.2 and 11.3.2 implications retain their
final discharge with qt-d-1222-shadow-components. -/
theorem no_fieldFourTriangle_of_preceding_sources
    {L V : Subgroup G} (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (hd : S.field.degree = 2)
    (K X : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (h701 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent)
    (h325 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      D_J.Source325Alternatives)
    (h1132 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput) (c_J : Coordinates D_J S_J.field)
      (f_J : InvariantFlag c_J) H,
      Hypothesis1131At D_J S_J (c_J.binarySubspace (f_J.space 0)) H →
      Proposition1132At D_J S_J (c_J.binarySubspace (f_J.space 0)) H)
    (h1122 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D_J.centralQuotientAction
        (ChapterB.QuasisimpleSource.binaryG2 S_J.field)) →
      ChapterE.indexedWeakClosure W (T : Subgroup G) 0 ≤
          (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
        @ChapterE.globalS G _ W D_J.elementary = (2 * S_J.field.degree : ℕ) ∧
        (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W) :
    ¬ Components.FieldFourTriangle T L (f.Li 0) (f.Li 1) K X := by
  intro ht
  obtain ⟨K₀,hK₀,hK₀K,_,hne,ho,hJ,W,⟨D_J⟩⟩ :=
    exists_triangle_choice D S f K X ht hK
  have h701_J := h701 _ _ D_J hJ
  have h325_J := h325 _ _ D_J hJ
  have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
  cases c with
  | sl3 m =>
    have ho' : Components.TriangleOrientation (K₀ ⊔ f.Li 1) L := by
      rcases ho with h | h
      · exact Or.inr ⟨h.2,h.1⟩
      · exact Or.inl ⟨h.2,h.1⟩
    have hc := Classification.orientation_order ho'
    rw [Nat.card_congr m.groupEquiv.toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear, hF] at hc
    norm_num [Classification.FieldFourOrder] at hc
  | g2 m =>
    have hc : Nat.card (L ⧸ pCore 2 L) = 251596800 := by
      rw [Nat.card_congr m.groupEquiv.toEquiv, Atlas.G2.card_Model, hF]
      norm_num
    have hsp : Source.IsSp ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 2 4 := by
      rcases ho with h | h
      · exact h.2
      · obtain ⟨E, hE, hfin, he, ⟨e⟩⟩ := h.1
        let := hE
        let := hfin
        rw [Nat.card_congr e.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp, he] at hc
        norm_num at hc
    obtain ⟨S_J,hd_J,⟨m_J⟩⟩ := Classification.symplectic_marked_of_source701325 D_J hJ
      ho hsp S.many h701_J h325_J
    obtain ⟨hw,hs,hr⟩ := h1122 _ _ D S ⟨m⟩
    exact ofFlag_no_forward_choice D S m f hd hK.1.1 hK₀ hK₀K hne hKZ
      D_J S_J m_J hd_J _ _ (h1132 _ _ D S (.g2 m) f)
      (h1132 _ _ D_J S_J (.sp4 m_J) (Sp4.flag m_J S_J)) hw hs hr
  | sp4 m =>
    have hc : Nat.card (L ⧸ pCore 2 L) = 979200 := by
      rw [Nat.card_congr m.groupEquiv.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp, hF]
      norm_num
    have hg : ClassificationModels.IsG2At
        ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 4 := by
      rcases ho with h | h
      · obtain ⟨E, hE, hfin, he, ⟨e⟩⟩ := h.1
        let := hE
        let := hfin
        rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, he] at hc
        norm_num at hc
      · exact h.2
    obtain ⟨S_J,hd_J,⟨m_J⟩⟩ := Classification.g2_marked_of_source701325 D_J hJ
      ho hg S.many h701_J h325_J
    obtain ⟨hw,hs,hr⟩ := h1122 _ _ D_J S_J ⟨m_J⟩
    exact ofFlag_no_reverse_choice D S m f hd hK.1.1 hK₀ hK₀K hne hKZ
      D_J S_J m_J hd_J _ _ (h1132 _ _ D S (.sp4 m) f)
      (h1132 _ _ D_J S_J (.g2 m_J) (G2.flag S_J m_J)) hw hs hr

/-- The complete preceding 11.1.2 alternative now yields the exact equality,
odd-extension and prime-PSL₂ list of 11.4.1(2), after proving triangle
exclusion on the unchanged chosen geometry. -/
theorem classical_refinement_of_preceding_sources
    {L V : Subgroup G} (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (K X : Subgroup G)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (h701 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent)
    (h325 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      D_J.Source325Alternatives)
    (h1132 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput) (c_J : Coordinates D_J S_J.field)
      (f_J : InvariantFlag c_J) H,
      Hypothesis1131At D_J S_J (c_J.binarySubspace (f_J.space 0)) H →
      Proposition1132At D_J S_J (c_J.binarySubspace (f_J.space 0)) H)
    (h1122 : ∀ (J W : Subgroup G) (D_J : Chapter12.Section02.ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D_J.centralQuotientAction
        (ChapterB.QuasisimpleSource.binaryG2 S_J.field)) →
      ChapterE.indexedWeakClosure W (T : Subgroup G) 0 ≤
          (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
        @ChapterE.globalS G _ W D_J.elementary = (2 * S_J.field.degree : ℕ) ∧
        (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W)
    (href : Components.RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree) :
    Source.ClassicalRefinementCase L (f.Li 0) K 1 S.field.degree := by
  cases href with
  | equal he => exact .equal (by simpa using he)
  | sl2 _ hn p hp hm => exact .sl2Prime rfl hn p hp hm
  | psl2 _ hn p hp hl hm hx => exact .psl2Prime rfl hn p hp hl hm hx
  | triangle _ hn ht =>
    exact (no_fieldFourTriangle_of_preceding_sources D S f hn K X hK hKZ
      h701 h325 h1132 h1122 ht).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
