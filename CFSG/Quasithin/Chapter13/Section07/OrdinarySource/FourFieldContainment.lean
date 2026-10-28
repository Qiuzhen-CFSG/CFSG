module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.ComponentContainment
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.FourFieldExclusion
public import Theory.Representation.SL3FourNaturalContainment
public import Theory.Representation.Sp4FourNaturalContainment

/-!
# Original containment and exclusion of the field-four natural components

Extend the original marked raw component section to a faithful whole ambient
model action. Its original quasithin cover bounds the cubic rank. The finite
natural SL₃(4) and Sp₄(4) theorems place the ambient two-residual in the literal
component image; the actual point residual is two-perfect, so its containment
lifts through the original two-core quotient. The existing contained-row
exclusions now apply without assuming point-residual containment.

The original setup, full F.9 packet, conjugator, raw and plus actions, offender,
and component marking are retained. This supplies the field-four cases of
Aschbacher--Smith13.7.6(5), printed pp.939--940, for the source18 sieve on p.945.
No use is made of the later13.7.19 conclusion.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.Source Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component
open Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.QuasisimpleSource ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The original point residual lies in the marked natural linear three component. -/
theorem source_linear_three_four_containment
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hsquare : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (hKH : K ≤ H) (hKC : (K.subgroupOf H).IsCComponent)
    (hKstar : IsComponent (Section08.Source.Hstar H) (Section08.Source.starImage H K))
    (hKn : H ≤ normalizer (K : Set G))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅Section08.Source.starImage H K,B⁆ = Section08.Source.starImage H K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (F : BinaryField) (hF : F.degree = 2)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearNatural F 3) eK)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H)))) : sourceOne L T V₁ ≤ K := by
  have htau : Function.Injective (linearNatural F 3) := by
    intro a b hab
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have hh := congrArg (fun f : Module.End (ZMod 2) (Fin 3 → F.Carrier) =>
      f (Pi.single j 1) i) hab
    change (a.val.mulVec (Pi.single j 1)) i = (b.val.mulVec (Pi.single j 1)) i at hh
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hh
  obtain ⟨γ,hγ,hres⟩ := source_component_model_action d h hU hV hne g hsquare hout
    σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ (linearNatural F 3) htau eK hs c
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := starImage H K
  let : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  let : J.Normal := (inferInstance : (K.subgroupOf H).Normal).map π (QuotientGroup.mk'_surjective _)
  have hfour : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  have hr : primeRank 3 (Hstar H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 H) pCore_isPGroup).trans
      ((source_plus_local_sqtk d h).stronglyQuasithin 3 Nat.prime_three (by decide))
  have hJ := SL3FourNaturalContainment.pResidual_le_of_natural hfour J
    ((Section08.Components.componentStarEquiv H K hKH hKC).symm.trans eK)
    γ hγ hres hr
  apply source_point_residual_le_of_star_le hH hKH hKn
  exact (le_pResidual_of_isPPerfect _ (source_local_star_twoPerfect hH)).trans hJ

/-- The original marked linear three field-four row is impossible. -/
theorem source_linear_three_four_false
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hsquare : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (hKH : K ≤ H) (hKC : (K.subgroupOf H).IsCComponent)
    (hKstar : IsComponent (Section08.Source.Hstar H) (Section08.Source.starImage H K))
    (hKn : H ≤ normalizer (K : Set G))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅Section08.Source.starImage H K,B⁆ = Section08.Source.starImage H K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (F : BinaryField) (hF : F.degree = 2)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearNatural F 3) eK)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H)))) : False := by
  have hL₁K := source_linear_three_four_containment d hH h hU hV hne g hsquare hout
    σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ F hF eK hs c
  exact linear_three_four_false d eL h1221 hH h hU hV hm
    hKH hKC hL₁K ρ hρ c F hF eK hs

/-- The original point residual lies in the marked natural symplectic four component. -/
theorem source_symplectic_four_four_containment
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hsquare : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (hKH : K ≤ H) (hKC : (K.subgroupOf H).IsCComponent)
    (hKstar : IsComponent (Section08.Source.Hstar H) (Section08.Source.starImage H K))
    (hKn : H ≤ normalizer (K : Set G))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅Section08.Source.starImage H K,B⁆ = Section08.Source.starImage H K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (F : BinaryField) (hF : F.degree = 2)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (binarySymplectic F) eK)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H)))) : sourceOne L T V₁ ≤ K := by
  have htau : Function.Injective (binarySymplectic F) := by
    intro a b hab
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have hh := congrArg (fun f : Module.End (ZMod 2) ((Fin 2 ⊕ Fin 2) → F.Carrier) =>
      f (Pi.single j 1) i) hab
    change (a.val.mulVec (Pi.single j 1)) i = (b.val.mulVec (Pi.single j 1)) i at hh
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hh
  obtain ⟨γ,hγ,hres⟩ := source_component_model_action d h hU hV hne g hsquare hout
    σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ (binarySymplectic F) htau eK hs c
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := starImage H K
  let : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  let : J.Normal := (inferInstance : (K.subgroupOf H).Normal).map π (QuotientGroup.mk'_surjective _)
  have hfour : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  have hr : primeRank 3 (Hstar H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 H) pCore_isPGroup).trans
      ((source_plus_local_sqtk d h).stronglyQuasithin 3 Nat.prime_three (by decide))
  have hJ := Sp4FourNaturalContainment.pResidual_le_of_natural hfour J
    ((Section08.Components.componentStarEquiv H K hKH hKC).symm.trans eK)
    γ hγ hres hr
  apply source_point_residual_le_of_star_le hH hKH hKn
  exact (le_pResidual_of_isPPerfect _ (source_local_star_twoPerfect hH)).trans hJ

/-- The original marked symplectic four field-four row is impossible. -/
theorem source_symplectic_four_four_false
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hsquare : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (hKH : K ≤ H) (hKC : (K.subgroupOf H).IsCComponent)
    (hKstar : IsComponent (Section08.Source.Hstar H) (Section08.Source.starImage H K))
    (hKn : H ≤ normalizer (K : Set G))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅Section08.Source.starImage H K,B⁆ = Section08.Source.starImage H K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (F : BinaryField) (hF : F.degree = 2)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (binarySymplectic F) eK)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H)))) : False := by
  have hL₁K := source_symplectic_four_four_containment d hH h hU hV hne g hsquare hout
    σ s B hB hBA hKH hKC hKstar hKn hk hcomm ρ hρ F hF eK hs c
  exact symplectic_four_four_false d eL h1221 hH h hU hV hm
    hKH hKC hL₁K ρ hρ c F hF eK hs

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
