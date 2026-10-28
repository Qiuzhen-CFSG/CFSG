module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.ContainedRows
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.FourFieldExclusion
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SixExclusion
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SL2FourExclusion
public import CFSG.Quasithin.Chapter13.Section07.ComponentFieldModels
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.ReducedMarks
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction

/-!
# Dispatching the contained marked source component

Every small-plane action row retains its actual component-section marking.
The contained natural SL₂(4) and A₆ rows contradict the literal chief counts;
the ordinary local geometry excludes the higher linear, alternating-natural
and field-four rows. Only the two separately owned earlier-source exclusions
for binary SL₃ and the four-dimensional A₇ action remain explicit below.

This theorem is the contained-row consumer of the original source13.7.18
packet, rather than a carrier-only recognition statement.
Source: Aschbacher–Smith13.7.6,13.7.18,13.7.21, printed pp.938–940,945–946.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.TransvectionRecognition ChapterF.Section09.Setup
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component
open Section08.TransvectionRecognition.Component.RecognitionStep
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
theorem contained_marked_row_false
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hsquare : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKstar : IsComponent (H ⧸ pCore 2 H) (Section08.Source.starImage H K))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅Section08.Source.starImage H K,B⁆ = Section08.Source.starImage H K)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) A E) (J : Subgroup A)
    [IsIrreducible (τ.comp J.subtype)]
    (hf : Function.Injective (τ.comp J.subtype))
    (eK : (K ⧸ pCore 2 K) ≃* J)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (τ.comp J.subtype) eK)
    (hrows : SmallMoved.PlaneActionCase τ J)
    (hthree : ∀ e3 : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      HasSectionModel H V₃ V₁ ρ K hKH (specialLinearNatural 3) e3 → False)
    (hseven : ∀ τ7 : Representation (ZMod 2) (alternatingGroup (Fin 7)) E,
      Function.Injective τ7 → IsIrreducible τ7 → Module.finrank (ZMod 2) E = 4 →
      ∀ e7 : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7),
      HasSectionModel H V₃ V₁ ρ K hKH τ7 e7 → False)
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (hmove : ¬ ⁅Section08.Source.VH H V,H⁆ ≤ Section08.Source.UH H V₃) : False := by
  let : IsQuasisimple (Section08.Source.starImage H K) := hKstar.2
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (Section08.Components.componentStarEquiv H K hKH hK).symm
  let : IsQuasisimple J := IsQuasisimple.of_mulEquiv eK
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  let : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
  have hU : IsMulCommutative (Section08.Source.UH H V₃) := inferInstance
  have ha6 : ∀ e6 : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
      HasSectionModel H V₃ V₁ ρ K hKH (alternatingNatural 6) e6 → False := by
    intro e6 hs6
    exact source_six_selected_false d hH h hV hne g hsquare hout σ s B hB hBA
      hKH hK hKstar hk hcomm hL₁K ρ hρ e6 hs6 hcentral hspan hmove
  cases hrows with
  | linearTwo F hF em =>
    let em' := SmallMoved.linearTwoFourActionEquiv F hF em
    exact source_sl2Four_selected_false d hH h hV hne g hsquare hout σ s B hB hBA
      hKH hK hKstar hk hcomm hL₁K ρ hρ (eK.trans em'.groupEquiv)
      (hs.actionEquiv em') hcentral hspan c
  | linearThree F hF em =>
    by_cases hF2 : F.degree = 2
    · exact linear_three_four_false d eL h1221 hH h hU hV hm hKH hK hL₁K ρ hρ c
        F hF2 (eK.trans em.groupEquiv) (hs.actionEquiv em)
    · have hF1 : F.degree = 1 := by have := F.degree_pos; omega
      let em' := SmallMoved.linearThreeTwoActionEquiv F hF1 em
      exact hthree (eK.trans em'.groupEquiv) (hs.actionEquiv em')
  | symplectic F hF em =>
    exact symplectic_four_four_false d eL h1221 hH h hU hV hm hKH hK hL₁K ρ hρ c
      F hF (eK.trans em.groupEquiv) (hs.actionEquiv em)
  | symplecticTwo em =>
    let em' := ExtensionConsequences.SymplecticTwo.markedAlternatingActionEquiv em
    exact ha6 (eK.trans em'.groupEquiv) (hs.actionEquiv em')
  | symmetric n hn em =>
    let em' := ExtensionConsequences.markedRestriction em
    have hd := alternating_natural_degree_six d eL h1221 hH h hm hKH hK hL₁K
      ρ hρ (by omega : 5 ≤ n) (eK.trans em'.groupEquiv) (hs.actionEquiv em')
    omega
  | alternatingSix em =>
    exact ha6 (eK.trans em.groupEquiv) (hs.actionEquiv em)
  | alternatingSeven eg hd =>
    let τ7 := (τ.comp J.subtype).comp eg.symm.toMonoidHom
    let em : ActionEquiv (τ.comp J.subtype) τ7 :=
      ⟨eg,LinearEquiv.refl _ _,fun g v => by
        change τ g.val v = τ (eg.symm (eg g)).val v
        rw [eg.symm_apply_apply]⟩
    have hi : IsIrreducible τ7 :=
      (irreducible_comp_surjective_iff eg.symm.toMonoidHom eg.symm.surjective _).mpr inferInstance
    exact hseven τ7 (hf.comp eg.symm.injective) hi hd (eK.trans eg) (hs.actionEquiv em)
  | binaryLinear n hn em =>
    rcases hn with rfl | rfl
    · exact linear_four_false d eL h1221 hH h hm hKH hK hL₁K ρ hρ
        (eK.trans em.groupEquiv) (hs.actionEquiv em)
    · exact linear_five_false d eL hH hm hKH hL₁K ρ hρ
        (eK.trans em.groupEquiv) (hs.actionEquiv em)
  | orthogonalSix em =>
    have hd := alternating_natural_degree_six d eL h1221 hH h hm hKH hK hL₁K
      ρ hρ (by decide : 5 ≤ 8) (eK.trans em.groupEquiv) (hs.actionEquiv em)
    omega
  | symmetricEight em =>
    let em' := ExtensionConsequences.markedRestriction em
    have hd := alternating_natural_degree_six d eL h1221 hH h hm hKH hK hL₁K
      ρ hρ (by decide : 5 ≤ 8) (eK.trans em'.groupEquiv) (hs.actionEquiv em')
    omega
  | exteriorFive eg hd =>
    let τ5 := (τ.comp J.subtype).comp eg.symm.toMonoidHom
    let em : ActionEquiv (τ.comp J.subtype) τ5 :=
      ⟨eg,LinearEquiv.refl _ _,fun g v => by
        change τ g.val v = τ (eg.symm (eg g)).val v
        rw [eg.symm_apply_apply]⟩
    let : IsIrreducible τ5 :=
      (irreducible_comp_surjective_iff eg.symm.toMonoidHom eg.symm.surjective _).mpr inferInstance
    exact ten_dimensional_false d eL hH hm hKH hL₁K ρ hρ τ5 hd
      (eK.trans eg) (hs.actionEquiv em)

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
