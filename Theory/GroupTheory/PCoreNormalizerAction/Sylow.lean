module
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Sylow markings for intrinsic core-quotient actions

Conjugation on J/O_p(J) preserves the image of a Sylow subgroup whenever
the original actors normalize its ambient image. The quotient Sylow
normalizer is exactly the image of the original one, so normalization of
the actors passes to its inner Borel. Both statements retain the original
quotient and conjugation maps.

Source application: Aschbacher--Smith 14.6.15, printed p.1035.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Normalizing the embedded Sylow subgroup preserves its literal core-quotient image. -/
theorem pCoreNormalizerAction_preserves_sylow
    (J K : Subgroup G) (hK : K ≤ normalizer (J : Set G)) (P : Sylow p J)
    (hKP : K ≤ normalizer ((P : Subgroup J).map J.subtype : Set G)) :
    ∀ α ∈ ((pCoreNormalizerAction p J).comp (inclusion hK)).range,
      ((P.mapSurjective (f := QuotientGroup.mk' (pCore p J))
        (QuotientGroup.mk'_surjective _)) : Subgroup (J ⧸ pCore p J)).map
          α.toMonoidHom = P.map (QuotientGroup.mk' (pCore p J)) := by
  rintro α ⟨k,rfl⟩
  let a := J.normalizerMonoidHom (inclusion hK k)
  have ha : (P : Subgroup J).map a.toMonoidHom = P := by
    apply map_injective J.subtype_injective
    rw [map_map]
    have he : J.subtype.comp a.toMonoidHom = (MulAut.conj (k : G)).toMonoidHom.comp J.subtype := by
      ext x; rfl
    rw [he,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp (hKP k.property)
  let q := QuotientGroup.mk' (pCore p J)
  change ((P : Subgroup J).map q).map
    (pCoreNormalizerAction p J (inclusion hK k)).toMonoidHom = (P : Subgroup J).map q
  rw [map_map]
  have he : (pCoreNormalizerAction p J (inclusion hK k)).toMonoidHom.comp q =
      q.comp a.toMonoidHom := by
    ext x; exact pCoreNormalizerAction_mk p J (inclusion hK k) x
  rw [he,←map_map,ha]

/-- The original Sylow normalizer controls the inner Borel acting on the
actual quotient-action range. -/
theorem pCoreNormalizerAction_borel_normalizes
    (J K : Subgroup G) (hK : K ≤ normalizer (J : Set G)) (P : Sylow p J)
    (hB : (normalizer (P : Set J)).map J.subtype ≤ normalizer (K : Set G)) :
    (normalizer (P.map (QuotientGroup.mk' (pCore p J)) : Set (J ⧸ pCore p J))).map
      MulAut.conj ≤ normalizer (((pCoreNormalizerAction p J).comp (inclusion hK)).range : Set _) := by
  let N := normalizer (J : Set G)
  let a := pCoreNormalizerAction p J
  have hfr : (a.comp (inclusion hK)).range = (K.subgroupOf N).map a := by
    rw [MonoidHom.range_comp,inclusion_range]
  rw [hfr]
  rintro α ⟨x,hx,rfl⟩
  rw [←P.normalizer_map_surjective (QuotientGroup.mk' (pCore p J))
    (QuotientGroup.mk'_surjective _)] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  rw [←pCoreNormalizerAction_on_component p J y]
  apply (K.subgroupOf N).le_normalizer_map a
  apply mem_map_of_mem
  apply le_normalizer_comap N.subtype
  exact hB (mem_map_of_mem J.subtype hy)

end Subgroup
