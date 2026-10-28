module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction.Family
public import Theory.AtlasPort.LinearGroups.G2.HighestRootWeakClosure
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# Ambient highest-root weak closure for the G₂ lower obstruction

Sylow alignment identifies the embedded highest-root group with the center
of T intersect L. Thus the whole of T normalizes it, including every outer
two-action. Factoring G = LT reduces the full ambient conjugacy orbit to the
embedded model orbit. The model weak closure is the five-root radical, whose
normalizer is the short parabolic; adjoining T gives the ambient normalizer.

This proves the weak-closure geometry used for Aschbacher–Smith E.1.14(1),
printed p.214 / PDF p.225, citing Asc82a Lemma 4.7. The E₁ and E₂ confinement
arguments and the final lower bound remain with the lower-obstruction assembly.
The model calculation uses the licensed ATLAS coordinates; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction
variable {G F : Type*} [Group G] [Field F]

theorem modelEmbedding_range (L : Subgroup G) (e : L ≃* Model F) :
    (modelEmbedding L e).range = L := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact (e.symm a).property
  · intro hx
    exact ⟨e ⟨x,hx⟩, by simp [modelEmbedding]⟩

theorem modelEmbedding_comap_aligned (L T : Subgroup G) (e : L ≃* Model F)
    (he : (T.subgroupOf L).map e.toMonoidHom = unipotent) :
    T.comap (modelEmbedding L e) = unipotent := by
  rw [← he]
  ext x
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    change (e.symm (e y) : G) ∈ T
    simpa only [e.symm_apply_apply] using (show (y : G) ∈ T from hy)

theorem unipotent_map_aligned (L T : Subgroup G) (e : L ≃* Model F)
    (he : (T.subgroupOf L).map e.toMonoidHom = unipotent) :
    unipotent.map (modelEmbedding L e) = T ⊓ L := by
  rw [← modelEmbedding_comap_aligned L T e he, map_comap_eq, modelEmbedding_range, inf_comm]

theorem root_eq_center_intersection [CharP F 2] (L T : Subgroup G) (e : L ≃* Model F)
    (he : (T.subgroupOf L).map e.toMonoidHom = unipotent) :
    (center (T ⊓ L : Subgroup G)).map (T ⊓ L).subtype = root L e := by
  rw [← unipotent_map_aligned L T e he,
    map_center_image_of_injective unipotent _ (modelEmbedding_injective L e),
    ← map_map, unipotent_center]
  rfl

/-- All of T, including its outer action on L, preserves the highest-root group. -/
theorem le_root_normalizer [CharP F 2] (L T : Subgroup G) [L.Normal]
    (e : L ≃* Model F) (he : (T.subgroupOf L).map e.toMonoidHom = unipotent) :
    T ≤ normalizer (root L e : Set G) := by
  have hn : T ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    exact ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht),
      (inferInstance : L.Normal).conj_mem x hx.2 t⟩
  rw [← root_eq_center_intersection L T e he]
  exact hn.trans (normalizer_le_normalizer_characteristic_image (T ⊓ L) (center (T ⊓ L : Subgroup G)))

private theorem map_conjugate_model (L : Subgroup G) (e : L ≃* Model F)
    (H : Subgroup (Model F)) (g : Model F) :
    (H.map (MulAut.conj g).toMonoidHom).map (modelEmbedding L e) =
      (H.map (modelEmbedding L e)).map
        (MulAut.conj (modelEmbedding L e g)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

/-- Under G = LT, the full ambient orbit equals the embedded model orbit.
The outer two-actions are eliminated by the intrinsic Sylow-center description. -/
theorem family_eq_model_orbit [CharP F 2] (L T : Subgroup G) [L.Normal]
    (hLT : L ⊔ T = ⊤) (e : L ≃* Model F)
    (he : (T.subgroupOf L).map e.toMonoidHom = unipotent) :
    family L e = Set.range (fun g : Model F =>
      (highestRoot.map (MulAut.conj g).toMonoidHom).map (modelEmbedding L e)) := by
  ext A
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨l,hl,t,ht,rfl⟩ := mem_sup_of_normal_left.mp (show g ∈ L ⊔ T by rw [hLT]; trivial)
    refine ⟨e ⟨l,hl⟩, ?_⟩
    dsimp only
    rw [map_conjugate_model]
    have hf : modelEmbedding L e (e ⟨l,hl⟩) = l := by simp [modelEmbedding]
    rw [hf]
    change (root L e).map (MulAut.conj l).toMonoidHom = _
    have ht' := mem_normalizer_iff_map_conj_eq.mp (le_root_normalizer L T e he ht)
    change (root L e).map (MulAut.conj t).toMonoidHom = root L e at ht'
    calc
      _ = ((root L e).map (MulAut.conj t).toMonoidHom).map
          (MulAut.conj l).toMonoidHom := by rw [ht']
      _ = (root L e).map (MulAut.conj (l*t)).toMonoidHom := by
        rw [map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨g,rfl⟩
    exact ⟨modelEmbedding L e g, (map_conjugate_model L e highestRoot g).symm⟩

/-- Exact transport of the weak closure for the full ambient family. -/
theorem weakClosure_eq_map_span [CharP F 2] (L T : Subgroup G) [L.Normal]
    (hLT : L ⊔ T = ⊤) (e : L ≃* Model F)
    (he : (T.subgroupOf L).map e.toMonoidHom = unipotent) :
    weakClosure T (family L e) =
      (SubgroupFamily.span HighestRootWeakClosure.rootOrbit unipotent).map (modelEmbedding L e) := by
  have hcomap := modelEmbedding_comap_aligned L T e he
  apply le_antisymm
  · apply sSup_le
    intro A hA
    rw [family_eq_model_orbit L T hLT e he] at hA
    obtain ⟨g,rfl⟩ := hA.1
    apply map_mono
    apply SubgroupFamily.le_span (family := HighestRootWeakClosure.rootOrbit) ⟨g,rfl⟩
    rw [← hcomap]
    exact map_le_iff_le_comap.mp hA.2
  · apply map_le_iff_le_comap.mpr
    apply sSup_le
    rintro A ⟨⟨g,rfl⟩,hA⟩
    apply map_le_iff_le_comap.mp
    apply le_sSup
    constructor
    · rw [family_eq_model_orbit L T hLT e he]
      exact ⟨g,rfl⟩
    · apply map_le_iff_le_comap.mpr
      rwa [hcomap]

/-- Highest-root weak closure in the full ambient group, including outer two-actions. -/
theorem weakClosure_eq_radical [Finite F] [CharP F 2]
    (L T : Subgroup G) [L.Normal] (hLT : L ⊔ T = ⊤)
    (e : L ≃* Model F) (he : (T.subgroupOf L).map e.toMonoidHom = unipotent)
    (hq : 2 < Nat.card F) :
    weakClosure T (family L e) = radical₁.map (modelEmbedding L e) := by
  rw [weakClosure_eq_map_span L T hLT e he, HighestRootWeakClosure.span_eq_radical hq]

private theorem normalizer_image_eq (L T : Subgroup G) [L.Normal]
    (hLT : L ⊔ T = ⊤) (e : L ≃* Model F) (H : Subgroup (Model F))
    (hT : T ≤ normalizer (H.map (modelEmbedding L e) : Set G)) :
    normalizer (H.map (modelEmbedding L e) : Set G) =
      (normalizer (H : Set (Model F))).map (modelEmbedding L e) ⊔ T := by
  apply le_antisymm
  · intro g hg
    obtain ⟨l,hl,t,ht,hlt⟩ := mem_sup_of_normal_left.mp
      (show g ∈ L ⊔ T by rw [hLT]; trivial)
    have hln : l ∈ normalizer (H.map (modelEmbedding L e) : Set G) := by
      have h := (normalizer (H.map (modelEmbedding L e) : Set G)).mul_mem hg
        ((normalizer (H.map (modelEmbedding L e) : Set G)).inv_mem (hT ht))
      simpa only [← hlt, mul_inv_cancel_right] using h
    have ha : e ⟨l,hl⟩ ∈ normalizer (H : Set (Model F)) := by
      have hpre : e ⟨l,hl⟩ ∈
          (normalizer (H.map (modelEmbedding L e) : Set G)).comap (modelEmbedding L e) := by
        simpa [mem_comap, modelEmbedding] using hln
      have hh := le_normalizer_comap (H := H.map (modelEmbedding L e))
        (modelEmbedding L e) hpre
      rwa [comap_map_eq_self_of_injective (modelEmbedding_injective L e)] at hh
    rw [← hlt]
    apply mul_mem_sup _ ht
    exact ⟨e ⟨l,hl⟩, ha, by simp [modelEmbedding]⟩
  · exact sup_le (le_normalizer_map (modelEmbedding L e)) hT

/-- The ambient normalizer of the weak closure is precisely the short overgroup. -/
theorem weakClosure_normalizer_eq_shortOvergroup [Finite G] [Finite F] [CharP F 2]
    (L T : Subgroup G) [L.Normal] (hLT : L ⊔ T = ⊤)
    (e : L ≃* Model F) (he : (T.subgroupOf L).map e.toMonoidHom = unipotent)
    (hq : 2 < Nat.card F) :
    normalizer (weakClosure T (family L e) : Set G) = shortOvergroup L T e := by
  have hw := weakClosure_eq_radical L T hLT e he hq
  have hT := le_weakClosure_normalizer L T e
  rw [hw] at hT ⊢
  rw [normalizer_image_eq L T hLT e radical₁ hT, HighestRootWeakClosure.normalizer_radical]
  rfl

/-- Both identities with the literal Sylow and field-degree hypotheses of the
nonbinary G₂ source calculation. -/
theorem weakClosure_geometry [Finite G] [Finite F] [CharP F 2]
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hLT : L ⊔ (T : Subgroup G) = ⊤) (e : L ≃* Model F)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom = unipotent)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f) :
    weakClosure (T : Subgroup G) (family L e) = radical₁.map (modelEmbedding L e) ∧
      normalizer (weakClosure (T : Subgroup G) (family L e) : Set G) =
        shortOvergroup L (T : Subgroup G) e := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    simpa only [pow_one] using (Nat.pow_lt_pow_right (by decide : 1 < 2) hf)
  exact ⟨weakClosure_eq_radical L T hLT e he hq,
    weakClosure_normalizer_eq_shortOvergroup L T hLT e he hq⟩

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction
