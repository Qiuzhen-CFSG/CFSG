module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.WeakClosure
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.HeadNormalizer.RootImages
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer

/-!
# The weak-closure normalizer of the triality head family

Three returning Weyl images of the actual q⁵ head generate the whole
positive subgroup. Transport through the aligned model equivalence therefore
identifies the ambient weak closure with T ∩ L. The positive subgroup's
normalizer in the model is the Borel. Factoring each ambient element as l t
then identifies the ambient normalizer with the embedded Borel joined with T,
which is contained in the central parabolic overgroup.

Only normality of L and G = LT are needed for the ambient normalizer step.
The result includes every positive binary exponent and nonsplit extensions.
It supplies the literal hweak premise of
`LowerObstruction.exists_obstruction_of_head_geometry`; the independent
large-intersection premise remains with that theorem's assembly owner.

Source: Aschbacher–Smith E.1.14(2), printed p.214 (`refs/quasithin.pdf`),
citing Asc82a, GF(2)-representations of finite groups, Lemma 4.7; the concrete
root and Borel geometry is GLS3 §§2.4–2.6.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
variable {G : Type*} [Group G] {f : ℕ} {hf : 0 < f}

/-- Weak closure of the full head family is exactly the aligned positive subgroup.
No normality, simplicity or splitting assumption is needed for this equality. -/
theorem head_weakClosure_eq_sylow_inf (L : Subgroup G) (T : Sylow 2 G)
    (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) :
    weakClosure (T : Subgroup G) (ambientHeadFamily L e) = (T : Subgroup G) ⊓ L := by
  apply le_antisymm (le_inf (weakClosure_le _ _) (head_weakClosure_le_socle L T e))
  rw [← aligned_unipotent_map L T e he]
  apply Subgroup.map_le_iff_le_comap.mpr
  apply HeadNormalizer.unipotent_le_of_head_images
  intro β hβ
  let B := (headSubgroup (binaryParameters f hf) rfl).map β.toMonoidHom
  have hB : B ∈ headFamily f hf := ⟨β, rfl⟩
  have hBT : B.map (modelEmbedding L e) ≤ (T : Subgroup G) :=
    ((Subgroup.map_mono hβ).trans_eq (aligned_unipotent_map L T e he)).trans inf_le_left
  exact Subgroup.map_le_iff_le_comap.mp (le_sSup ⟨⟨B, hB, rfl⟩, hBT⟩)

private theorem normalizer_image_eq (L T : Subgroup G) [L.Normal]
    (hLT : L ⊔ T = ⊤) (e : L ≃* BinaryCarrier f hf)
    (H : Subgroup (BinaryCarrier f hf))
    (hT : T ≤ normalizer (H.map (modelEmbedding L e) : Set G)) :
    normalizer (H.map (modelEmbedding L e) : Set G) =
      (normalizer (H : Set (BinaryCarrier f hf))).map (modelEmbedding L e) ⊔ T := by
  apply le_antisymm
  · intro g hg
    obtain ⟨l, hl, t, ht, hlt⟩ := mem_sup_of_normal_left.mp
      (show g ∈ L ⊔ T by rw [hLT]; trivial)
    have hln : l ∈ normalizer (H.map (modelEmbedding L e) : Set G) := by
      have h := (normalizer (H.map (modelEmbedding L e) : Set G)).mul_mem hg
        ((normalizer (H.map (modelEmbedding L e) : Set G)).inv_mem (hT ht))
      simpa only [← hlt, mul_inv_cancel_right] using h
    have ha : e ⟨l, hl⟩ ∈ normalizer (H : Set (BinaryCarrier f hf)) := by
      have hpre : e ⟨l, hl⟩ ∈
          (normalizer (H.map (modelEmbedding L e) : Set G)).comap (modelEmbedding L e) := by
        simpa [mem_comap, modelEmbedding] using hln
      have hh := le_normalizer_comap (H := H.map (modelEmbedding L e))
        (modelEmbedding L e) hpre
      rwa [comap_map_eq_self_of_injective (modelEmbedding_injective L e)] at hh
    rw [← hlt]
    apply mul_mem_sup _ ht
    exact ⟨e ⟨l, hl⟩, ha, by simp [modelEmbedding]⟩
  · exact sup_le (le_normalizer_map (modelEmbedding L e)) hT

/-- The normalizer in an arbitrary normal LT-extension is the embedded Borel
joined with T. In particular no complement to L is chosen. -/
theorem head_weakClosure_normalizer_eq_borel_sup (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf))
    (hLT : L ⊔ (T : Subgroup G) = ⊤) :
    normalizer (weakClosure (T : Subgroup G) (ambientHeadFamily L e) : Set G) =
      (borel (binaryParameters f hf)).map (modelEmbedding L e) ⊔ (T : Subgroup G) := by
  have hT : (T : Subgroup G) ≤ normalizer
      ((unipotent (binaryParameters f hf)).map (modelEmbedding L e) : Set G) := by
    rw [aligned_unipotent_map L T e he]
    exact (le_inf (T : Subgroup G).le_normalizer (le_normalizer_of_normal (H := L))).trans
      inf_normalizer_le_normalizer_inf
  rw [head_weakClosure_eq_sylow_inf L T e he, ← aligned_unipotent_map L T e he,
    normalizer_image_eq L T hLT e _ hT,
    _root_.Triality.Standard.ConcreteBruhat.normalizer_unipotent_eq_borel _ rfl]

/-- The literal hweak input of exists_obstruction_of_head_geometry for E.1.14(2).
This stronger normal-subgroup form includes the simple generalized Fitting
subgroup, every positive exponent, and nonsplit outer two-extensions. -/
theorem head_weakClosure_normalizer_le_central (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf))
    (hLT : L ⊔ (T : Subgroup G) = ⊤) :
    normalizer (weakClosure (T : Subgroup G) (ambientHeadFamily L e) : Set G) ≤
      parabolicOvergroup L T e .central := by
  rw [head_weakClosure_normalizer_eq_borel_sup L T e he hLT]
  exact sup_le_sup (Subgroup.map_mono (borel_le_parabolic _ .central)) le_rfl

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
