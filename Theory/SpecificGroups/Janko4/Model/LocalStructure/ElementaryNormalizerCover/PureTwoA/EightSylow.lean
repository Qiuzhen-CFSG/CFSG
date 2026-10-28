module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightPlacement
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.FullSylowExclusions

/-!
# Full Sylow exclusion for the native eight-centralizer branch

The proved native-eight placement puts the whole normalizer of X in a
conjugate of the full F normalizer whenever C(X) has the specified native
fusion. The two-part of that local is too small to contain a full Sylow
subgroup of J4. Transporting the same Sylow by the inverse conjugator gives
the obstruction used for the original projected actor in Chapter 12.

Source: Kleidman--Wilson (1988), Corollary 2.3.6, p.493, and the local
inspection in Aschbacher--Smith 12.5.4, printed p.819.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA
attribute [local irreducible] modelGroup matrixA matrixB

/-- An elementary-eight full centralizer prevents its whole normalizer from
containing a full J4 Sylow. The native placement premise is discharged. -/
theorem not_sylow_le_fused_eight_normalizer
    (S : Sylow 2 Model) (X : Subgroup Model) (g : Model)
    (hC : (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom =
      ElementaryEightGeometry.nativeEight 1) :
    ¬ (S : Subgroup Model) ≤ normalizer (X : Set Model) := by
  intro hS
  obtain ⟨k,hk⟩ := fused_eight_normalizer eightNormalizerPlacement X g hC
  let e := MulAut.conj (g⁻¹*k)
  have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id Model := by
    ext x
    exact e.symm_apply_apply x
  have ht := map_mono (f := e.symm.toMonoidHom) (hS.trans hk)
  change (S : Subgroup Model).map e.symm.toMonoidHom ≤
    (LinearFive.fullNormalizer.map e.toMonoidHom).map e.symm.toMonoidHom at ht
  rw [map_map,hid,map_id] at ht
  exact LinearFive.not_sylow_le_fullNormalizer
    (S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective) ht

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA
