module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.Preimage
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Lifting the one-factor residual from H/O₂(H)

The actual preimage of a subgroup image is its product with O₂(H).
Finite two-residuals commute with this quotient map. A two-perfect subgroup
normalized by O₂(H) is recovered as the two-residual of that product, so
containments and equalities of residual images lift to the ambient group.
For the source Sylow subgroup T ≤ H, O₂(H) ≤ T; hence T-invariance gives
exactly the normalization needed for the lift. No ambient normality of the
marked subgroup is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the one-factor part of Lemma 13.8.5, printed pp.947–948 (PDF pp.964–965).
The marked-model calculation must still supply the image alternatives.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor
variable {G : Type*} [Group G]

/-- The image/preimage correspondence retains the source containment X ≤ H. -/
theorem starImage_le_iff {H X : Subgroup G} (hX : X ≤ H)
    (K : Subgroup (Source.Hstar H)) :
    Source.starImage H X ≤ K ↔ X ≤ starPreimage H K := by
  constructor
  · intro h x hx
    exact ⟨⟨x, hX hx⟩, h ⟨⟨x, hX hx⟩, hx, rfl⟩, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := h hx
    have he' : y = x := Subtype.ext he
    exact he' ▸ hy

/-- The full preimage of X* is X O₂(H), with its literal ambient inclusion. -/
theorem starPreimage_starImage {H X : Subgroup G} (hX : X ≤ H) :
    starPreimage H (Source.starImage H X) = X ⊔ Source.QH H := by
  unfold starPreimage Source.starImage Source.QH
  rw [comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    map_subgroupOf_eq_of_le hX]
  rfl

/-- Two-perfect subgroups normalized by the two-kernel are determined by
their images. Normality in the ambient group is not required. -/
theorem eq_of_starImage_eq (H X Y : Subgroup G)
    (hXH : X ≤ H) (hYH : Y ≤ H) (hX : IsPPerfect 2 X) (hY : IsPPerfect 2 Y)
    (hnX : Source.QH H ≤ normalizer (X : Set G))
    (hnY : Source.QH H ≤ normalizer (Y : Set G))
    (he : Source.starImage H X = Source.starImage H Y) : X = Y := by
  have hj : X ⊔ Source.QH H = Y ⊔ Source.QH H := by
    rw [← starPreimage_starImage hXH, ← starPreimage_starImage hYH, he]
  rw [← embedded_pResidual_join_pGroup X (Source.QH H) hX (isPGroup_pCoreIn 2 H) hnX,
    ← embedded_pResidual_join_pGroup Y (Source.QH H) hY (isPGroup_pCoreIn 2 H) hnY, hj]

/-- The ambient two-residual maps onto the two-residual of the image. -/
theorem starImage_residual [Finite G] {H X : Subgroup G} (hX : X ≤ H) :
    Source.starImage H ((pResidual 2 X).map X.subtype) =
      (pResidual 2 (Source.starImage H X)).map (Source.starImage H X).subtype := by
  have he : ((pResidual 2 X).map X.subtype).subgroupOf H =
      (pResidual 2 (X.subgroupOf H)).map (X.subgroupOf H).subtype := by
    apply (map_injective H.subtype_injective)
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hX),
      map_embedded_pResidual, map_subgroupOf_eq_of_le hX]
  unfold Source.starImage
  rw [he, map_embedded_pResidual]

/-- The image of O²(K) is O²(K*) for the actual preimage K. -/
theorem starImage_preimageResidual [Finite G]
    (H : Subgroup G) (K : Subgroup (Source.Hstar H)) :
    Source.starImage H (preimageResidual H K) = (pResidual 2 K).map K.subtype := by
  rw [preimageResidual, starImage_residual (starPreimage_le H K), starImage_starPreimage]

/-- The embedded residual lies in the actual preimage. -/
theorem preimageResidual_le (H : Subgroup G) (K : Subgroup (Source.Hstar H)) :
    preimageResidual H K ≤ starPreimage H K := map_subtype_le _

/-- A source Sylow subgroup contained in H contains the ambient image of O₂(H). -/
theorem core_le_sourceSylow (H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) : Source.QH H ≤ T := by
  have hcore := (pCore_isPGroup (p := 2) (G := H)).le_sylow_of_normal (T.subtype hTH)
  rintro x ⟨h, hh, rfl⟩
  exact hcore hh

/-- A residual-image containment lifts through a normalizing two-kernel. -/
theorem preimageResidual_le_of_image [Finite G]
    (H : Subgroup G) (K : Subgroup (Source.Hstar H))
    (Y : Subgroup G) (hYH : Y ≤ H) (hY : IsPPerfect 2 Y)
    (hn : Source.QH H ≤ normalizer (Y : Set G))
    (himage : (pResidual 2 K).map K.subtype ≤ Source.starImage H Y) :
    preimageResidual H K ≤ Y := by
  let R := preimageResidual H K
  have hRH : R ≤ H := (preimageResidual_le H K).trans (starPreimage_le H K)
  have hR : IsPPerfect 2 R := isPPerfect_embedded_pResidual 2 _
  have hle : R ≤ Y ⊔ Source.QH H := by
    rw [← starPreimage_starImage hYH]
    apply (starImage_le_iff hRH _).mp
    exact (starImage_preimageResidual H K).le.trans himage
  have hm := embedded_pResidual_mono 2 hle
  rw [(pResidual_eq_top_iff 2 R).mpr hR,
    ← MonoidHom.range_eq_map, range_subtype,
    embedded_pResidual_join_pGroup Y (Source.QH H) hY (isPGroup_pCoreIn 2 H) hn] at hm
  exact hm

/-- Two-perfect lifts with the same residual image agree. -/
theorem preimageResidual_eq_of_image [Finite G]
    (H : Subgroup G) (K : Subgroup (Source.Hstar H)) [K.Normal]
    (Y : Subgroup G) (hYH : Y ≤ H) (hY : IsPPerfect 2 Y)
    (hn : Source.QH H ≤ normalizer (Y : Set G))
    (himage : Source.starImage H Y = (pResidual 2 K).map K.subtype) :
    preimageResidual H K = Y := by
  let R := preimageResidual H K
  have hRH : R ≤ H := (preimageResidual_le H K).trans (starPreimage_le H K)
  have hR : IsPPerfect 2 R := isPPerfect_embedded_pResidual 2 _
  have hnR : Source.QH H ≤ normalizer (R : Set G) :=
    (pCoreIn_le 2 H).trans (le_normalizer_preimageResidual H K)
  have hjoin : R ⊔ Source.QH H = Y ⊔ Source.QH H := by
    rw [← starPreimage_starImage hRH, ← starPreimage_starImage hYH]
    rw [himage, starImage_preimageResidual]
  change R = Y
  rw [← embedded_pResidual_join_pGroup R (Source.QH H) hR (isPGroup_pCoreIn 2 H) hnR,
    ← embedded_pResidual_join_pGroup Y (Source.QH H) hY (isPGroup_pCoreIn 2 H) hn,
    hjoin]

/-- T-invariance supplies the required normalization in the source setting. -/
theorem preimageResidual_eq_of_image_of_sourceSylow [Finite G]
    (H : Subgroup G) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (K : Subgroup (Source.Hstar H)) [K.Normal]
    (Y : Subgroup G) (hYH : Y ≤ H) (hY : IsPPerfect 2 Y)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (himage : Source.starImage H Y = (pResidual 2 K).map K.subtype) :
    preimageResidual H K = Y :=
  preimageResidual_eq_of_image H K Y hYH hY ((core_le_sourceSylow H T hTH).trans hn) himage

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor

end
