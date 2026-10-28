module

public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison.Quotients
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiZeroQuotient

/-!
# Transporting the star Borel to the original core quotient

The literal image of an intersection in K/O₂(K) maps to its literal star
image. An injective core-to-star map consequently transports a Sylow
normalizer back to this intersection, rather than merely to an isomorphic
subgroup. For a χ₀ block, simplicity and perfectness make the core quotient
centerless, so C.2.7's central-kernel bound gives the required injectivity.

Source: Aschbacher--Smith C.2.7(1,3), pp.145--147, applied in 14.6.15,
printed p.1035.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The two original quotient projections agree on the specified subgroup. -/
theorem coreImage_map_coreToStar {K R B : Subgroup G}
    (hRK : R ≤ normalizer K) (hBK : B ≤ K) :
    (coreImage K B).map (coreToStar hRK) =
      (starImage K R B).subgroupOf (starImage K R K) := by
  ext y
  constructor
  · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    change (toStarImage K R k : StarQuotient K R) ∈ starImage K R B
    exact ⟨⟨k, (show K ≤ K ⊔ R from le_sup_left) k.property⟩, hk, rfl⟩
  · rintro ⟨b, hb, hy⟩
    let k : K := ⟨b, hBK hb⟩
    refine ⟨QuotientGroup.mk' (pCore 2 K) k, ⟨k, hb, rfl⟩, ?_⟩
    exact Subtype.ext hy

/-- An injective comparison map restores the literal core-quotient Borel. -/
theorem core_borel_of_injective {K R M : Subgroup G}
    (hRK : R ≤ normalizer K) (hinj : Function.Injective (coreToStar hRK))
    (hb : IsRankOneBorel (starImage K R K) (starM K R M)) :
    ∃ S : Sylow 2 (K ⧸ pCore 2 K),
      coreImage K (M ⊓ K) = normalizer (S : Set (K ⧸ pCore 2 K)) := by
  let e := MulEquiv.ofBijective (coreToStar hRK) ⟨hinj, coreToStar_surjective hRK⟩
  obtain ⟨S, hS⟩ := hb
  have hB : (coreImage K (M ⊓ K)).map e.toMonoidHom = normalizer (S : Set _) := by
    change (coreImage K (M ⊓ K)).map (coreToStar hRK) = _
    rw [coreImage_map_coreToStar hRK inf_le_right]
    change (starM K R M).subgroupOf (starImage K R K) = _
    rw [hS, subgroupOf, comap_map_eq_self_of_injective
      (f := (starImage K R K).subtype) (starImage K R K).subtype_injective]
  let S₀ := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨S₀, ?_⟩
  have hh := congrArg (map e.symm.toMonoidHom) hB
  rw [map_map] at hh
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
    ext x
    exact e.symm_apply_apply x
  rw [he, map_id] at hh
  exact hh.trans (map_normalizer_eq_of_bijective _ e.symm.bijective)

/-- The central comparison kernel is trivial for the original χ₀ block. -/
theorem core_borel_of_chiZero {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hc : ChapterC.IsChiZeroBlock K)
    (hb : IsRankOneBorel (starImage K R K) (starM K R M)) :
    ∃ S : Sylow 2 (K ⧸ pCore 2 K),
      coreImage K (M ⊓ K) = normalizer (S : Set (K ⧸ pCore 2 K)) := by
  let : IsSimpleGroup (K ⧸ pCore 2 K) := hc.quotient_simple
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    rcases (inferInstance : (center (K ⧸ pCore 2 K)).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K)
        (center_eq_top_iff.mp hz)).elim
  apply core_borel_of_injective h.normalizes _ hb
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact bot_unique (hz ▸ ChapterC.C27Source.coreToStar_ker_central_from_source h)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
