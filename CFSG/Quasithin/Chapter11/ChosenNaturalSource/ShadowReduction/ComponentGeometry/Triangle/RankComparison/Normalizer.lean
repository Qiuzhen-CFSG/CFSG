module
public import Theory.Representation.BinaryConjugationSection.NormalizerAction
public import Theory.Representation.BinaryOffender.InnerNormalizerActors

/-!
# Full-normalizer transport with the original conjugation coordinates

A surjective model marking of H identifies its literal action image. Relative
normality of H in N then puts the action of N inside the full linear normalizer
of that model. This construction allows a kernel on H and does not assume that
arbitrary ambient automizers are inner. The output retains conjugation on the
same ambient subgroup A and agrees with the model embedding on H.

Source application: Aschbacher--Smith, 11.4.1(2), printed p.776.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
variable {G K W : Type*} [Group G] [Group K] [AddCommGroup W] [Module (ZMod 2) W]

/-- An actual normal marked model extends to the full linear normalizer. -/
theorem exists_marked_normalizer
    (H A N : Subgroup G) (hHN : H ≤ N) (hNA : N ≤ normalizer (A : Set G))
    (hNH : N ≤ normalizer (H : Set G))
    (σ : Representation (ZMod 2) K W)
    (q : H →* K) (hq : Function.Surjective q) (e : A ≃* Multiplicative W)
    (hact : ∀ (h : H) (a : A),
      (e ⟨h.val * a.val * h.val⁻¹,
        (mem_normalizer_iff.mp (hNA (hHN h.property)) a.val).mp a.property⟩).toAdd =
        σ (q h) (e a).toAdd) :
    ∃ β : N →* linearNormalizer σ,
      (∀ (n : N) (a : A),
        (e ⟨n.val * a.val * n.val⁻¹,
          (mem_normalizer_iff.mp (hNA n.property) a.val).mp a.property⟩).toAdd =
          normalizerRepresentation σ (β n) (e a).toAdd) ∧
      (∀ h : H, β (inclusion hHN h) = normalizerEmbedding σ (q h)) := by
  let η : N →* (W ≃ₗ[ZMod 2] W) :=
    (BinaryConjugationSection.normalizerAction e.toMonoidHom e.bijective).comp (inclusion hNA)
  let γ : Representation (ZMod 2) N W :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp η
  have he (n : N) (a : A) : γ n (e a).toAdd =
      (e (A.normalizerMonoidHom (inclusion hNA n) a)).toAdd :=
    BinaryConjugationSection.normalizerAction_coordinates e.toMonoidHom e.bijective _ a
  have hres (h : H) : γ (inclusion hHN h) = σ (q h) := by
    apply LinearMap.ext
    intro v
    obtain ⟨a,ha⟩ := e.surjective (Multiplicative.ofAdd v)
    have hv : (e a).toAdd = v := congrArg Multiplicative.toAdd ha
    rw [← hv,he]
    exact hact h a
  let J := H.subgroupOf N
  let : J.Normal := (normal_subgroupOf_iff_le_normalizer hHN).mpr hNH
  have himage : J.map γ.asGroupHom = actionImage σ := by
    ext z
    constructor
    · rintro ⟨h,hh,rfl⟩
      exact ⟨q ⟨h,hh⟩, Units.ext (hres ⟨h,hh⟩).symm⟩
    · rintro ⟨k,rfl⟩
      obtain ⟨h,rfl⟩ := hq k
      exact ⟨inclusion hHN h, h.property, Units.ext (hres h)⟩
  have hn (n : N) : γ.asGroupHom n ∈ linearNormalizer σ := by
    change γ.asGroupHom n ∈ normalizer (actionImage σ : Set _)
    rw [← himage]
    exact J.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (le_normalizer_of_normal (mem_top n)))
  let β : N →* linearNormalizer σ := γ.asGroupHom.codRestrict _ hn
  refine ⟨β, fun n a => (he n a).symm, ?_⟩
  intro h
  apply Subtype.ext
  apply Units.ext
  exact hres h

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
