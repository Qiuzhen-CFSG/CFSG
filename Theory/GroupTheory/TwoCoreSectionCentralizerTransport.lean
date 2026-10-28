module
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Transport of the centralizer of a two-core quotient

An ambient group isomorphism preserves the normalizer and the commutator
condition defining trivial action on B/O₂(B). The proof transports the
actual embedded two-core along the restriction of the same isomorphism.
Source application: Aschbacher--Smith, 10.2.9, printed p.751.
-/

public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]
theorem twoCoreSectionCentralizer_map_equiv_le (B : Subgroup G) (e : G ≃* H) :
    (commutatorPreimage (normalizer (B : Set G)) B (B.pCoreIn 2)).map e.toMonoidHom ≤
      commutatorPreimage (normalizer (B.map e.toMonoidHom : Set H))
        (B.map e.toMonoidHom) ((B.map e.toMonoidHom).pCoreIn 2) := by
  have hc : (B.pCoreIn 2).map e.toMonoidHom = (B.map e.toMonoidHom).pCoreIn 2 := by
    unfold pCoreIn
    rw [←pCore_map_iso 2 (B.equivMapOfInjective e.toMonoidHom e.injective),map_map,map_map]
    rfl
  apply le_commutatorPreimage
  · rw [←map_equiv_normalizer_eq]
    exact map_mono (commutatorPreimage_le _ _ _)
  · rw [←map_commutator,←hc]
    exact map_mono (commutator_commutatorPreimage_le _ _ _
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
end Subgroup
