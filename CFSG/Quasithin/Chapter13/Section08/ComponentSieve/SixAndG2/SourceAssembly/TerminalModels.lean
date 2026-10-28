module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.Six
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Assembly

/-!
# The marked ordinary terminal edge

The earlier 13.7.6 flag theorem and the recognized component section give
one coordinate system for both the actual whole action and the seed plane.
The base edge normalizes that plane. Its Sylow index is three, so its image
is the full syntheme stabilizer, with its precise alternating or symmetric
marking. In the cover case the weight-four plane remains in the original
five-dimensional module. The strict-terminal application uses that marking
and the original component section on the unchanged critical pair.

The universal 13.7.6 flag theorem remains an earlier source input of
qt-d-1381-source. No plane model, edge identification or point-normalizer
model is retained as an additional hypothesis here.
Source: Aschbacher–Smith, 13.7.6 and 13.8.26–34, pp.938–939,962–969.
-/

public section
open Subgroup Representation BinaryPermutation Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
namespace TerminalModels
open CriticalGeometry SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionParabolic TransvectionParabolic.Marking
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

private theorem invariant_eq {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (r : Representation (ZMod 2) A W) (J : Subgroup A) (P : Submodule (ZMod 2) W)
    (hi : ∀ a ∈ J, ∀ v ∈ P, r a v ∈ P) (a : A) (ha : a ∈ J) :
    P.map (r a) = P := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hi a ha v hv
  · intro v hv
    refine ⟨r a⁻¹ v, hi a⁻¹ (J.inv_mem ha) v hv, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

private theorem cover_plane_eq : OrbitModels.plane = Representation.SixLetterRadicalDisplacement.W := by
  have hp : OrbitModels.point = Representation.SixLetterRadicalDisplacement.q 0 1 +
      Representation.SixLetterRadicalDisplacement.q 2 3 := by decide
  have hs : OrbitModels.seed = Representation.SixLetterRadicalDisplacement.q 0 1 +
      Representation.SixLetterRadicalDisplacement.q 4 5 := by decide
  simp only [OrbitModels.plane, hp, hs, Representation.SixLetterRadicalDisplacement.W]

private theorem sylow_parabolic_card {J : Type*} [Group J] [Finite J]
    (S : Sylow 2 J) (B : Subgroup J) (hSB : (S : Subgroup J) ≤ B)
    (hi : (S : Subgroup J).relIndex B = 3) :
    Nat.card B = Nat.card S * 3 := by
  have hh := ((S : Subgroup J).subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hSB).toEquiv] at hh
  change Nat.card S * (S : Subgroup J).relIndex B = Nat.card B at hh
  rw [hi] at hh
  exact hh.symm

private theorem symmetric_edge {J : Type*} [Group J] [Finite J]
    (e : J ≃* Equiv.Perm (Fin 6)) (S : Sylow 2 J) (B : Subgroup J)
    (hSB : (S : Subgroup J) ≤ B) (hi : (S : Subgroup J).relIndex B = 3)
    (hle : B.map e.toMonoidHom ≤ BinaryFlags.H2) : B.map e.toMonoidHom = BinaryFlags.H2 := by
  have hc : Nat.card S = 16 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide +kernel
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective e.injective, sylow_parabolic_card S B hSB hi, hc]
  exact synthemeStabilizer_order.le

private theorem alternating_edge {J : Type*} [Group J] [Finite J]
    (e : J ≃* alternatingGroup (Fin 6)) (S : Sylow 2 J) (B : Subgroup J)
    (hSB : (S : Subgroup J) ≤ B) (hi : (S : Subgroup J).relIndex B = 3)
    (hle : B.map ((alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom) ≤ BinaryFlags.H2) :
    B.map e.toMonoidHom = a6SynthemeStabilizer := by
  have hc : Nat.card S = 8 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv,
      nat_card_alternatingGroup, Nat.card_fin]
    decide +kernel
  apply eq_of_le_of_card_ge
  · rintro _ ⟨a, ha, rfl⟩
    exact hle (mem_map_of_mem _ ha)
  · rw [card_map_of_injective e.injective, sylow_parabolic_card S B hSB hi, hc]
    exact a6SynthemeStabilizer_order.le

variable {G : Type*} [Group G] [Finite G]
  {H V₃ V₂ V₁ B : Subgroup G} [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [Finite G] in
private theorem flag_stabilizer
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (φ : Source.Hstar H →* Equiv.Perm (Fin 6))
    (hm : ModelFlag V₂ ρ φ) (hn : B ≤ normalizer (V₃ : Set G)) :
    (Source.starImage H B).map φ ≤ BinaryFlags.H2 := by
  let J := (Source.starImage H B).map φ
  have natural_stable (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
      (he : ∀ a u, E (ρ a u) = naturalRepresentation (Fin 6) (φ a) (E u))
      (hp : (sectionImage H V₃ V₁ V₃).map E.toLinearMap = canonicalPlane) : J ≤ BinaryFlags.H2 := by
    have hi := CompatibleFlags.marked_section_invariant ρ hρ φ
      (naturalRepresentation (Fin 6)) E he B V₃ hn
    change ∀ g ∈ (B.subgroupOf H).map (φ.comp (QuotientGroup.mk' (pCore 2 H))), _ at hi
    rw [← Subgroup.map_map] at hi
    change ∀ g ∈ J, ∀ v ∈ (sectionImage H V₃ V₁ V₃).map E.toLinearMap,
      naturalRepresentation (Fin 6) g v ∈ (sectionImage H V₃ V₁ V₃).map E.toLinearMap at hi
    rw [hp] at hi
    intro g hg
    exact (canonicalPlane_stabilizer g).mp (invariant_eq _ J canonicalPlane hi g hg)
  rcases hm with ⟨E, he, _, hp⟩ | ⟨E, he, _, hp, _⟩
  · apply natural_stable E he
    exact hp.trans CompatibleFlags.plane_image_eq_canonical
  · have hi := CompatibleFlags.marked_section_invariant ρ hρ φ
      (coreRepresentation (Fin 6)) E he B V₃ hn
    rw [← Subgroup.map_map] at hi
    change ∀ g ∈ J, ∀ v ∈ (sectionImage H V₃ V₁ V₃).map E.toLinearMap,
      coreRepresentation (Fin 6) g v ∈ (sectionImage H V₃ V₁ V₃).map E.toLinearMap at hi
    rw [hp] at hi
    intro g hg
    apply (canonicalPlane_stabilizer g).mp
    apply invariant_eq (naturalRepresentation (Fin 6)) J canonicalPlane _ g hg
    intro a ha v hv
    rw [← CompatibleFlags.plane_image_eq_canonical] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨coreRepresentation (Fin 6) a w, hi a ha w hw, ?_⟩
    exact coreToNatural_equivariant _ _

/-- Simultaneous source flag coordinates and the literal index-three edge
supply exactly the ordinary terminal model, in both full-actor cases. -/
theorem marked_models_of_flag
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6)) (hf : Function.Injective φ)
    (ha : alternatingGroup (Fin 6) ≤ φ.range)
    (hm : ModelFlag V₂ (A6Endgame.IntersectionBalance.tildeRepresentation H _ V₁ a) φ)
    (hn : B ≤ normalizer (V₃ : Set G))
    (S : Sylow 2 (Source.Hstar H)) (hSB : (S : Subgroup _) ≤ Source.starImage H B)
    (hi : (S : Subgroup _).relIndex (Source.starImage H B) = 3) :
    TerminalRanks.MarkedModels H B V₃ V₁ := by
  have hle := flag_stabilizer _ (TerminalPoint.starAction_isConjugation a) φ hm hn
  refine ⟨a, ?_⟩
  rcases NaturalSix.extension_equiv_of_embedding φ hf ha with ⟨e, he⟩ | ⟨e, he⟩
  · apply Or.inl
    refine ⟨e, alternating_edge e S _ hSB hi ?_⟩
    have hh : (alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom = φ := by
      apply MonoidHom.ext
      intro x
      exact he x
    rwa [hh]
  · apply Or.inr
    have hh : e.toMonoidHom = φ := by
      apply MonoidHom.ext
      intro x
      exact he x
    refine ⟨e, symmetric_edge e S _ hSB hi (by rwa [hh]), ?_⟩
    rcases hm with ⟨E, hE, _, hp⟩ | ⟨E, hE, _, hp, _⟩
    · refine A6Endgame.IntersectionBalance.CompatibleModel.of_natural H V₃ V₁ a e E
        (fun g v => by rw [he]; exact hE g v) ?_
      change (sectionImage H V₃ V₁ V₃).map E.toLinearMap = canonicalPlane
      exact hp.trans CompatibleFlags.plane_image_eq_canonical
    · refine A6Endgame.IntersectionBalance.CompatibleModel.of_augmentation H V₃ V₁ a e E
        (fun g v => by rw [he]; exact hE g v) ?_
      change (sectionImage H V₃ V₁ V₃).map E.toLinearMap = _
      exact hp.trans cover_plane_eq

variable {T : Sylow 2 G} {L K V M G₁ : Subgroup G}

private theorem ordinary_flag_of_quotient
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    Nonempty (EarlierCore.ComponentSetup T L V V₁ V₂ V₃) := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply (eq_bot_iff_card _).mpr
    calc
      Nat.card (center (L ⧸ pCore 2 L)) = Nat.card (center (alternatingGroup (Fin 6))) :=
        Nat.card_congr (centerCongr eL).toEquiv
      _ = 1 := by rw [alternatingGroup.center_eq_bot (by simp), card_bot]
  let e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6) :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans (local_central_quotient d))
  apply local_ordinary_flag_model d e
  intro l
  exact local_central_quotient_apply d l

/-- The recognized A₆ section supplies the ordinary terminal edge and
compatible module marking. Only the genuinely earlier universal 13.7.6
flag theorem remains explicit; the Sylow index and edge equality are proved. -/
theorem ordinary_terminal_models
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlierFlags : NaturalSection.Earlier1376 L (sourceOne L T V₁)
      (T : Subgroup G) G₁ M V₂ V₃ V₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal) (hKT : H = K ⊔ (T : Subgroup G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁
      (A6Endgame.IntersectionBalance.tildeRepresentation H _ V₁ a) K hKH
      (alternatingNaturalRepresentation (Fin 6)) eK) :
    TerminalRanks.MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁ := by
  let ρ := A6Endgame.IntersectionBalance.tildeRepresentation H _ V₁ a
  have hρ : IsConjugation H V₃ V₁ ρ := TerminalPoint.starAction_isConjugation a
  obtain ⟨_, hLK, hprod, hmodels⟩ := earlierFlags H hHz (d.line_le_uh H)
    ρ hρ K hKH hK 6 (by decide) eK hs
  have h6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      NaturalSection.SixPointMarking H K V₂ V₃ V₁ ρ := by
    rcases hmodels with ⟨_, hL, hm⟩ | ⟨hn, _⟩
    · exact ⟨hL, hm⟩
    · omega
  obtain ⟨eL⟩ := h6.1
  obtain ⟨dOrd⟩ := ordinary_flag_of_quotient d eL
  have hres : sourceOne L T V₁ = EarlierCore.localResidual L V₁ :=
    dOrd.extend.line_residual_eq
  obtain ⟨φ, hf, ⟨e, g, hmark⟩, hm, _⟩ := compatible_marking_of_earlier dOrd hK hprod
    hKH (hres ▸ hLK) (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    ρ hρ h6.2
  have ha : alternatingGroup (Fin 6) ≤ φ.range := by
    intro x hx
    have hy : g * x * g⁻¹ ∈ alternatingGroup (Fin 6) :=
      (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem x hx g
    obtain ⟨k, hk⟩ := e.surjective ⟨g * x * g⁻¹, hy⟩
    refine ⟨k.val, ?_⟩
    rw [hmark, hk]
    simp [mul_assoc]
  have hn : sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ normalizer (V₃ : Set G) := by
    rw [hres]
    exact sup_le dOrd.extend.one_normalizes_seed d.seed_stable
  let S := (T.subtype (le_sup_right.trans hHz.1.2)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS : (S : Subgroup _) = Source.starImage H (T : Subgroup G) := rfl
  rw [Comparison.local_edge d hF9]
  exact marked_models_of_flag a φ hf ha hm hn S
    (by rw [hS]; exact map_mono (subgroupOf_mono H le_sup_right))
    (six_source_parabolic_index d hHz hF9 hcomm hKH hK hN hKT eK)

/-- Application to the actual strict-denominator terminal theorem. The
base-edge model is constructed here, on the same pair, and the point model
is constructed by the existing terminal theorem from the same section. -/
theorem strict_terminal_of_section
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlierFlags : NaturalSection.Earlier1376 L (sourceOne L T V₁)
      (T : Subgroup G) G₁ M V₂ V₃ V₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal) (hKT : H = K ⊔ (T : Subgroup G))
    (hH : H = G₁)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁
      (A6Endgame.IntersectionBalance.tildeRepresentation H _ V₁ a) K hKH
      (alternatingNaturalRepresentation (Fin 6)) eK)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃) : False := by
  have hm := ordinary_terminal_models d earlierFlags hHz hF9 hcomm hKH hK hN hKT a eK hs
  have hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
    apply le_antisymm
    · rw [hKT]
      exact sup_le_sup le_rfl le_sup_right
    · exact sup_le hKH hHz.1.2
  have hqs := (SixRecognition.Constituents.component_properties _ hfit.symm
    ((Components.componentStarEquiv H K hKH hK).symm.trans eK)).1
  exact TerminalPoint.contradiction_of_component_section d hHz hF9 c hH hgen hK hN
    hqs hcentral hcomm hstrict hDstrict hm a hUK eK hs

end TerminalModels
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
