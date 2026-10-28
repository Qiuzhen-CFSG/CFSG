module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.InternalEstimate
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.InnerFromCoverage
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.SourceAssembly
public import Theory.Representation.BinaryOffender.InnerNormalizerActors

/-!
# Assembly of the local Tits displacement calculation

The actual full linear normalizer's elementary actors descend to the Parrott
group by the inner-involution calculation and binary Schur's lemma. The
five-local weight bounds and the finite centralizer geometry then give the
strict inequality on these same actors. The final theorem applies this to
the parent's original component action and literal cover equivalence.

The finite geometry, full binary involution coverage and two five-weight
estimates remain explicit inputs. Their producers must be completed before
this module supplies the unconditional source exclusion. See the sibling
`TitsCubicDisplacement/Source.md` for the inspected source and proof route.

Source: Aschbacher--Smith K.3, printed p.457; GM04 Lemma 8.8, internal p.57.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
open Subgroup Representation Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The local calculations apply to the literal full normalizer action.
This implication retains arbitrary actors outside the component at input. -/
theorem normalizer_displacement_of_local_calculations
    (d : LocalGeometry) (hcover : Tits.InvolutionRootGeometry.BinaryInvolutionCoverage)
    (σ : Representation (ZMod 2) Tits.ParrottGroup V)
    (hi : IsIrreducible σ) (hf : Function.Injective σ)
    (hfive : ∀ k ∈ Tits.fiveKernel, k ≠ 1 → 20 ≤ fixedCodim σ (zpowers k))
    (hinverter : 12 ≤ fixedCodim σ (zpowers fiveInverter))
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A := by
  obtain ⟨B, hB, hm⟩ := elementary_normalizer_is_image σ hf hi
    (inner_from_binary_coverage hcover) A hA
  have h := internal_displacement_of_local_calculations d σ hf hfive hinverter B hB
  have hr := rank_map_injective (normalizerEmbedding σ)
    (normalizerEmbedding_injective σ hf) B
  have hd := fixedCodim_map_equivariant σ (normalizerRepresentation σ)
    (normalizerEmbedding σ) (LinearEquiv.refl _ _) (fun _ _ => rfl) B
  rw [hm] at hr hd
  rwa [← hr, hd] at h

/-- Actual consumer application to the original K.3 action. The independent
local producers, rather than a displacement-classification premise, remain. -/
theorem source_exclusion_of_local_calculations
    (d : LocalGeometry) (hcover : Tits.InvolutionRootGeometry.BinaryInvolutionCoverage)
    (hweights : ∀ σ : Representation (ZMod 2) Tits.ParrottGroup V,
      Function.Injective σ →
      (∀ k ∈ Tits.fiveKernel, k ≠ 1 → 20 ≤ fixedCodim σ (zpowers k)) ∧
        12 ≤ fixedCodim σ (zpowers fiveInverter))
    {G : Type*} [Group G] [Finite G]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    [IsIrreducible (ρ.comp L.subtype)] (e : L ≃* Tits.ParrottGroup)
    (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2) : False := by
  apply tits_exclusion_of_cubic_displacement_bound ρ L e hf hc
  intro σ hi hσ A hA _
  obtain ⟨hfive, hinverter⟩ := hweights σ hσ
  exact normalizer_displacement_of_local_calculations d hcover σ hi hσ
    hfive hinverter A hA

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
