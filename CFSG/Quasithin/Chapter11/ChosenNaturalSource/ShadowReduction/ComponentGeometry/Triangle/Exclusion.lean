module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Orientation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.Contradiction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Bounds

/-!
# Excluding a common-plane triangle on the original chosen modules

The natural field-four markings rule out the linear-three fixed-space branch
by their actual group orders. The full preceding 11.3.2 implication therefore
kills both fixed spaces. Zeroth weak-closure centralization supplies its
normalizer bound and containment in the literal second radical. Common-plane
placement constructs the radical action and its image bound, so the mutual
G₂/symplectic rank comparison gives a contradiction.

The forward application retains I = K₀ ∨ L₂. The reverse application uses
the old symplectic module and transports its unchanged second radical along
the paired residual equality. Neither application assumes an action on R₂,
radical representatives, or a rank-comparison conclusion.

Paired residual placement and generation still have to be constructed in
this task; these conditional applications do not assert all of 11.4.1(2).
The preceding 11.2.2 and 11.3.2 inputs retain their final discharge with
`qt-d-1222-shadow-components`.
Source: Aschbacher--Smith 11.1.2(3) and 11.4.1(2), pp.762--764,776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
open Reselection Reselection.Classification LocalGeometry.Components

private theorem not_linear_four_of_order {A : Type*} [Group A]
    (hc : FieldFourOrder (Nat.card A)) : ¬ Source.IsSL A 3 4 := by
  rintro ⟨F, hF, hfin, hcard, ⟨e⟩⟩
  let := hF
  let := hfin
  rw [Nat.card_congr e.toEquiv,
    Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear, hcard] at hc
  norm_num [FieldFourOrder] at hc

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V I U : Subgroup G}

/-- In either field-four orientation the linear-three exception is impossible,
so the full shadow implication supplies fixed-space vanishing on this choice. -/
theorem fixed_trivial_of_triangle_order
    (D : Chapter12.Section02.ChosenModule T I U) (S : D.NonbinaryNaturalInput)
    (hd : S.field.degree = 2) (ho : TriangleOrientation L I)
    (U₁ : Submodule (ZMod 2) D.chosenCentralQuotient)
    (h1132 : ∀ H, Hypothesis1131At D S U₁ H → Proposition1132At D S U₁ H) :
    U ⊓ centralizer (I : Set G) = ⊥ := by
  apply fixed_trivial D S U₁ _ h1132
  intro hlin
  exact (not_linear_four_of_order (orientation_order ho)
    (by simpa only [hd, show (2 : ℕ) ^ 2 = 4 from rfl] using hlin)).elim

/-- The literal common-plane image suffices for the complete rank contradiction.
All action, kernel, fixed-space and weak-closure transport premises are derived. -/
theorem no_common_plane
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (binaryG2 S.field))
    (f : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.g2 m))
    (hd : S.field.degree = 2)
    (D_I : Chapter12.Section02.ChosenModule T I U) (S_I : D_I.NonbinaryNaturalInput)
    (m_I : ActionEquiv D_I.centralQuotientAction (binarySymplectic S_I.field))
    (hd_I : S_I.field.degree = 2)
    (V₁ : Submodule (ZMod 2) D.chosenCentralQuotient)
    (U₁ : Submodule (ZMod 2) D_I.chosenCentralQuotient)
    (h1132 : ∀ H, Hypothesis1131At D S V₁ H → Proposition1132At D S V₁ H)
    (h1132_I : ∀ H, Hypothesis1131At D_I S_I U₁ H → Proposition1132At D_I S_I U₁ H)
    (hout : ¬ I ≤ normalizer (L : Set G))
    (hw : indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hr : (2 * S.field.degree : ℕ∞) < globalR V)
    (hLI : f.Li 1 ≤ I)
    (hplane : ((f.Li 1).subgroupOf I).map
      (m_I.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) = planeLocal) :
    False := by
  have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
  have hF_I : Nat.card S_I.field.Carrier = 4 := by
    simpa [hd_I] using S_I.field.card_eq
  have hG : ClassificationModels.IsG2At (L ⧸ pCore 2 L) 4 :=
    ⟨S.field.Carrier, inferInstance, inferInstance, hF, ⟨m.groupEquiv⟩⟩
  have hSp : Source.IsSp (I ⧸ pCore 2 I) 2 4 :=
    ⟨S_I.field.Carrier, inferInstance, inferInstance, hF_I, ⟨m_I.groupEquiv⟩⟩
  have ho : TriangleOrientation L I := .inl ⟨hG, hSp⟩
  have ho' : TriangleOrientation I L := .inr ⟨hSp, hG⟩
  have hfix := fixed_trivial_of_triangle_order D S hd ho' V₁ h1132
  have hfix_I := fixed_trivial_of_triangle_order D_I S_I hd_I ho U₁ h1132_I
  have hker := centralizer_join_eq_core D_I S_I.sylow_normalizes (orientation_simple ho)
  have hN := (LocalGeometry.WeakClosure.G2.normalizer_bounds_of_zero_centralizes D S f hw).1
  have hW : indexedWeakClosure V (T : Subgroup G) 0 ≤ f.Ri 1 := by
    have hWQ : indexedWeakClosure V (T : Subgroup G) 0 ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      rw [← LocalGeometry.WeakClosure.seed_sylow_centralizer D S]
      exact hw
    exact hWQ.trans (LocalGeometry.WeakClosure.G2.originalCore_le_Ri D S f 1)
  have hlift := ofFlag_planeRadicalLifts D_I D S f ⊥ 1 ⊥ m_I S_I.nonbinary hLI hplane
  obtain ⟨_, α, hα, himage⟩ := exists_plane_radical_action D_I hfix_I m_I
    (ofFlag S f ⊥ 1 ⊥).R₂ hlift
  have hs4 : (4 : ℕ∞) ≤ @globalS G _ V D.elementary := by
    rw [hs, hd]
    norm_num
  have hr4 : (4 : ℕ∞) < globalR V := by
    norm_num [hd] at hr
    exact hr
  exact ofFlag_no_inner_four_actor D S m f ⊥ 1 ⊥ hF_I hF hfix
    (LocalGeometry.WeakClosure.seed_normalizer_le D S) I U hout hN hker
    (@IsElementaryAbelian.isPGroup 2 _ _ D_I.elementary) S_I.sylow_normalizes
    hW hs4 hr4 α (symplecticEquiv D_I hfix_I m_I) hα himage

/-- In the forward source orientation, proper component containment and the
literal triangle generation identity supply escape of the symplectic vertex. -/
theorem ofFlag_no_forward_plane
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (binaryG2 S.field))
    (f : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.g2 m))
    (hd : S.field.degree = 2) (K K₀ : Subgroup G)
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hlocal : f.Li 0 ∈ Chapter1.L G T) (hlt : f.Li 0 < K)
    (hgen : K = f.Li 0 ⊔ K₀)
    (D_I : Chapter12.Section02.ChosenModule T (K₀ ⊔ f.Li 1) U)
    (S_I : D_I.NonbinaryNaturalInput)
    (m_I : ActionEquiv D_I.centralQuotientAction (binarySymplectic S_I.field))
    (hd_I : S_I.field.degree = 2)
    (V₁ : Submodule (ZMod 2) D.chosenCentralQuotient)
    (U₁ : Submodule (ZMod 2) D_I.chosenCentralQuotient)
    (h1132 : ∀ H, Hypothesis1131At D S V₁ H → Proposition1132At D S V₁ H)
    (h1132_I : ∀ H, Hypothesis1131At D_I S_I U₁ H → Proposition1132At D_I S_I U₁ H)
    (hw : indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hr : (2 * S.field.degree : ℕ∞) < globalR V)
    (hplane : ((f.Li 1).subgroupOf (K₀ ⊔ f.Li 1)).map
      (m_I.groupEquiv.toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)))) = planeLocal) : False :=
  no_common_plane D S m f hd D_I S_I m_I hd_I V₁ U₁ h1132 h1132_I
    (third_vertex_escapes_of_proper_flag_component D S f K K₀ hK hlocal hlt hgen)
    hw hs hr le_sup_right hplane

/-- Once the forward flags have the same second residual, Sylow alignment
constructs the compatible plane marking. No marked-image premise remains. -/
theorem ofFlag_no_forward_paired_flags
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (binaryG2 S.field))
    (f : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.g2 m))
    (hd : S.field.degree = 2) (K K₀ : Subgroup G)
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hlocal : f.Li 0 ∈ Chapter1.L G T) (hlt : f.Li 0 < K)
    (hgen : K = f.Li 0 ⊔ K₀)
    (D_I : Chapter12.Section02.ChosenModule T (K₀ ⊔ f.Li 1) U)
    (S_I : D_I.NonbinaryNaturalInput)
    (m_I : ActionEquiv D_I.centralQuotientAction (binarySymplectic S_I.field))
    (f_I : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.sp4 m_I))
    (hd_I : S_I.field.degree = 2) (hsecond : f_I.Li 1 = f.Li 1)
    (V₁ : Submodule (ZMod 2) D.chosenCentralQuotient)
    (U₁ : Submodule (ZMod 2) D_I.chosenCentralQuotient)
    (h1132 : ∀ H, Hypothesis1131At D S V₁ H → Proposition1132At D S V₁ H)
    (h1132_I : ∀ H, Hypothesis1131At D_I S_I U₁ H → Proposition1132At D_I S_I U₁ H)
    (hw : indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hr : (2 * S.field.degree : ℕ∞) < globalR V) : False := by
  apply ofFlag_no_forward_plane D S m f hd K K₀ hK hlocal hlt hgen
    D_I S_I (alignedSymplecticMark S_I m_I) hd_I V₁ U₁ h1132 h1132_I hw hs hr
  simpa only [hsecond] using alignedSymplecticMark_plane_image S_I m_I f_I

/-- The reverse orientation uses the unchanged old symplectic module.
Its aligned plane residual is the same literal new G₂ second residual;
the component escape is proved in the new point normalizer. -/
theorem ofFlag_no_reverse_paired_flags
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (binarySymplectic S.field))
    (f : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.sp4 m))
    (hd : S.field.degree = 2) (K K₀ : Subgroup G)
    (hgen : K = f.Li 0 ⊔ K₀)
    (D_I : Chapter12.Section02.ChosenModule T (K₀ ⊔ f.Li 1) U)
    (S_I : D_I.NonbinaryNaturalInput)
    (m_I : ActionEquiv D_I.centralQuotientAction (binaryG2 S_I.field))
    (f_I : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.g2 m_I))
    (hd_I : S_I.field.degree = 2)
    (hfirst : f_I.Li 0 = K₀) (hsecond : f_I.Li 1 = f.Li 1)
    (hK : Source.ComponentIn (normalizer (f_I.Vi 0 : Set G)) K)
    (hlocal : K₀ ∈ Chapter1.L G T) (hlt : K₀ < K)
    (V₁ : Submodule (ZMod 2) D.chosenCentralQuotient)
    (U₁ : Submodule (ZMod 2) D_I.chosenCentralQuotient)
    (h1132 : ∀ H, Hypothesis1131At D S V₁ H → Proposition1132At D S V₁ H)
    (h1132_I : ∀ H, Hypothesis1131At D_I S_I U₁ H → Proposition1132At D_I S_I U₁ H)
    (hw : indexedWeakClosure U (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (U : Set G))
    (hs : @globalS G _ U D_I.elementary = (2 * S_I.field.degree : ℕ))
    (hr : (2 * S_I.field.degree : ℕ∞) < globalR U) : False := by
  have hout : ¬ L ≤ normalizer ((K₀ ⊔ f.Li 1 : Subgroup G) : Set G) := by
    intro hL
    apply proper_flag_component_escapes D_I S_I f_I K hK
      (hfirst.symm ▸ hlocal) (hfirst.symm ▸ hlt)
    rw [hgen]
    refine sup_le (((LocalGeometry.localResidual_le _).trans inf_le_left).trans hL) ?_
    exact (le_sup_left : K₀ ≤ K₀ ⊔ f.Li 1).trans (K₀ ⊔ f.Li 1).le_normalizer
  apply no_common_plane D_I S_I m_I f_I hd_I D S
    (alignedSymplecticMark S m) hd U₁ V₁ h1132_I h1132 hout hw hs hr
  · rw [hsecond]
    exact (LocalGeometry.localResidual_le _).trans inf_le_left
  · rw [hsecond]
    exact alignedSymplecticMark_plane_image S m f

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
