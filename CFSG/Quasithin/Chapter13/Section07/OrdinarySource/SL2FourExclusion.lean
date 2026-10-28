module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SL2FourActorSource
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SL2FourDualChiefLower
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.LocalExclusion
public import Theory.Representation.SL2FourNaturalOrbits.PointCommutator
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SL2FourA4Quotient
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.SL2FourCubicLength
public import Theory.Representation.SL2FourNaturalOrbits.NaturalCompatibility

/-!
# The selected natural SL₂(4) component and the literal chief counts

The original selected actor permits at most four noncentral binary chief
factors. The natural component cover and the A₄ residual quotient force five.
The source geometry inputs below are discharged by the actual natural-cover
and seed-plane recognition producer; no chief-count hypothesis is retained.
Source: Aschbacher–Smith, 13.7.13 and the SL₂(4) branch of 13.7.21,
printed pp.943 and 945–946.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion Section08.TransvectionRecognition ChapterF.Section09.Setup
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The literal A₄ quotient and cubic natural action contradict the original actor bound. -/
theorem source_sl2Four_selected_false_of_residual
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
    (_hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
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
    (_hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* Representation.SL2FourNatural.SL)
    (_hs : HasSectionModel H V₃ V₁ ρ K hKH
      (Representation.SL2FourNatural.PointCommutator.representation) eK)
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (f : sourceOne L T V₁ →* alternatingGroup (Fin 4))
    (hf : Function.Surjective f)
    (hker : f.ker = (H.pCoreIn 2).subgroupOf (sourceOne L T V₁))
    (hcubic : ∀ A : Subgroup G, A ≤ sourceOne L T V₁ → Nat.card A = 3 →
      conjugationCubicLength A (Section08.Source.UH H V₃) = 2) : False := by
  let J := sourceOne L T V₁
  have hdiv : 3 ∣ Nat.card J := by
    apply dvd_trans _ (card_dvd_of_surjective f hf)
    rw [nat_card_alternatingGroup]
    norm_num
  obtain ⟨C,hC⟩ := Sylow.exists_subgroup_card_pow_prime (G := J) 3 (n := 1)
    (by simpa using hdiv)
  let A := C.map J.subtype
  have hAJ : A ≤ J := by
    rintro _ ⟨c,hc,rfl⟩
    exact c.property
  have hA : Nat.card A = 3 := by
    rw [card_map_of_injective Subtype.val_injective]
    simpa using hC
  obtain ⟨t,h0,h1⟩ := exists_chiefSeries (⊥ : NormalNode J) ⊤ bot_le
  have hl := source_sl2Four_chief_count_ge_five_of_residual d h inferInstance
    (hL₁K.trans hKH) f hf hker A hAJ hA
    ((hAJ.trans hL₁K).trans hcentral) (hcubic A hAJ hA) t h0 h1
  have hu := source_sl2Four_false_of_five_chief_factors d h inferInstance hV hne g hsquare hout
    σ s B hB hBA hKH hK hKstar hk hcomm eK hspan
  rw [PlusAction.source_local_residual_eq d h] at hu
  exact hu t h0 h1 hl

/-- The original selected natural SL₂(4) packet is impossible, with the residual
and cubic-length inputs proved on the actual quotient and covering action. -/
theorem source_sl2Four_selected_false
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    [IsElementaryAbelian 2 (Section08.Source.UH H V₃)]
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
    (eK : (K ⧸ pCore 2 K) ≃* Representation.SL2FourNatural.SL)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (Representation.SL2OrthogonalCover.binaryNatural (F := Representation.SL2FourNatural.F)) eK)
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (hspan : V ≤ V₃ ⊔ conjugate V₁ (g : G))
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H)))) : False := by
  have hm : HasSectionModel H V₃ V₁ ρ K hKH
      Representation.SL2FourNatural.PointCommutator.representation eK := by
    rw [SL2FourNatural.pointCommutator_eq_binaryNatural]
    exact hs
  obtain ⟨f,hf,hker⟩ := OrdinarySource.source_sl2Four_residual_surjection
    d hH h hKH hK hL₁K ρ hρ eK hm
  apply source_sl2Four_selected_false_of_residual d hH h hV hne g hsquare hout
    σ s B hB hBA hKH hK hKstar hk hcomm hL₁K ρ hρ eK hm hcentral hspan f hf hker
  intro A hAL hA
  exact OrdinarySource.source_sl2Four_uh_cubic_length
    d hH h hKH hK hL₁K ρ hρ eK hm c A hAL hA

end CFSG.Quasithin.Chapter13.Section07
