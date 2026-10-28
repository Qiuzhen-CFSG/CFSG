module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL3.Geometry
public import Theory.SpecificGroups.PSL3Even.LargePlaneNormalizers

/-!
# The large-intersection normalizer input for the PSL₃ lower obstruction

A subgroup Q of the marked Sylow subgroup whose intersection with a root plane
has more than 2^f elements has its full ambient normalizer in either the plane
normalizer or the Sylow normalizer. The intrinsic proof recovers the plane as a
centralizer in the exponent-two case, and recovers the Sylow as the two-core of
the centralizer of the square subgroup otherwise. Normality of L transports
every ambient conjugation through the actual matrix-group isomorphism, so graph
and field automorphisms are included.

This proves precisely `LargeIntersectionNormalizer` from `PSL3.Geometry`, the
geometric input to the lower E-generation obstruction. The remaining source
assembly belongs to the PSL₃ lower-obstruction consumer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
E.1.1–6, printed pp.209–210, and E.1.14(1), p.214; unitriangular geometry
as in §5.3.5–7, p.660.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSL3Obstruction
open Matrix.PSL3Even.UnipotentGeometry
variable {G F : Type*} [Group G] [Field F]

private theorem normalizer_le_of_model_automorphisms (L : Subgroup G) [L.Normal]
    (e : L ≃* PSL(3,F)) (Q P : Subgroup PSL(3,F))
    (h : ∀ α : MulAut PSL(3,F), Q.map α.toMonoidHom = Q → P.map α.toMonoidHom = P) :
    normalizer (Q.map (modelEmbedding L e) : Set G) ≤
      normalizer (P.map (modelEmbedding L e) : Set G) := by
  intro g hg
  have hgL : g ∈ normalizer (L : Set G) := by rw [normalizer_eq_top]; trivial
  let α : MulAut PSL(3,F) :=
    (e.symm.trans (L.normalizerMonoidHom ⟨g,hgL⟩)).trans e
  have hcompat : (modelEmbedding L e).comp α.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (modelEmbedding L e) := by
    ext x
    change ((e.symm (e ((L.normalizerMonoidHom ⟨g,hgL⟩) (e.symm x)))) : G) = _
    rw [e.symm_apply_apply]
    rfl
  have hα : Q.map α.toMonoidHom = Q := by
    apply Subgroup.map_injective (modelEmbedding_injective L e)
    rw [map_map, hcompat, ← map_map]
    exact mem_normalizer_iff_map_conj_eq.mp hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (P.map (modelEmbedding L e)).map (MulAut.conj g).toMonoidHom = _
  rw [map_map, ← hcompat, ← map_map, h α hα]

/-- The full ambient normalizer alternative for a subgroup meeting a marked
PSL₃ plane in more than the field order. Normality of L includes every ambient
conjugation action, including graph and field automorphisms. -/
theorem largeIntersectionNormalizer [Finite G] [Finite F]
    (L : Subgroup G) [L.Normal] (e : L ≃* PSL(3,F))
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2^f) :
    LargeIntersectionNormalizer L e f := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  intro Q hQ b hc
  let Qm : Subgroup PSL(3,F) := Q.comap (modelEmbedding L e)
  let Pm : Subgroup PSL(3,F) :=
    (if b then V₁ F else V₂ F).map (projective F)
  have hQm : Qm ≤ Matrix.PSL3.LinearThree.unipotent F := by
    have h := Subgroup.comap_mono (f := modelEmbedding L e) hQ
    change Qm ≤ ((Matrix.PSL3.LinearThree.unipotent F).map
      (modelEmbedding L e)).comap (modelEmbedding L e) at h
    rwa [Subgroup.comap_map_eq_self_of_injective (modelEmbedding_injective L e)] at h
  have hQr : Qm.map (modelEmbedding L e) = Q :=
    Subgroup.map_comap_eq_self ((hQ.trans (sylowImage_le L e)).trans_eq
      (modelEmbedding_range L e).symm)
  have hPr : Pm.map (modelEmbedding L e) = planeImage L e b := by
    change ((if b then V₁ F else V₂ F).map (projective F)).map (modelEmbedding L e) = _
    rw [map_map]
    rfl
  have hcM : Nat.card F < Nat.card (Qm ⊓ Pm : Subgroup PSL(3,F)) := by
    have hm : (Qm ⊓ Pm).map (modelEmbedding L e) = Q ⊓ planeImage L e b := by
      rw [map_inf _ _ _ (modelEmbedding_injective L e), hQr, hPr]
    rw [← hm, Subgroup.card_map_of_injective (modelEmbedding_injective L e)] at hc
    rwa [hF]
  rcases Matrix.PSL3Even.LargePlaneNormalizers.automorphism_alternative F Qm hQm b
    (by omega : 0 < f) hF hcM with hp | hs
  · left
    rw [← hQr, ← hPr]
    exact normalizer_le_of_model_automorphisms L e Qm Pm hp
  · right
    rw [← hQr]
    exact normalizer_le_of_model_automorphisms L e Qm
      (Matrix.PSL3.LinearThree.unipotent F) hs

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSL3Obstruction
