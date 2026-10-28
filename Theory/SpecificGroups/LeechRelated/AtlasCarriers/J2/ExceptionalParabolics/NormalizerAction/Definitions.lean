module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.NormalizerAction.RadicalAction
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The fixed Hall--Janko normalizer in the full automorphism group

All subgroups use the literal conjugation embedding of the degree-100
ATLAS carrier. The inner radical is a normal two-subgroup of its full
normalizer. Its inclusion in the two-residual follows by mapping the
already checked inner-normalizer residual, without identifying a residual
with a derived subgroup.

Source: GLS3 Table 5.3g; Aschbacher--Smith 15.3.42, printed p.1138.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.NormalizerAction
open Theory.GroupTheory Subgroup GeneratorPair Seed PairNormalizer

/-- The actual radical embedded as inner automorphisms. -/
def innerRadical : Subgroup (MulAut Carrier) := q₂.map MulAut.conj

/-- Its normalizer in all automorphisms of the unchanged carrier. -/
def fullNormalizer : Subgroup (MulAut Carrier) := normalizer (innerRadical : Set _)

/-- The intrinsic two-residual, embedded back into all automorphisms. -/
def fullResidual : Subgroup (MulAut Carrier) :=
  (pResidual 2 fullNormalizer).map fullNormalizer.subtype

/-- Faithfulness of the checked permutation extension implies faithful inner action. -/
theorem inner_conj_injective : Function.Injective (MulAut.conj : Carrier →* MulAut Carrier) := by
  intro x y h
  have he : intoExtension x = intoExtension y :=
    extensionAction_injective (by simpa only [extensionAction_inner] using h)
  exact inclusion_injective
    (congrArg (fun z : Extension => (z : Equiv.Perm (Fin 100))) he)

/-- The inner radical lies in the full normalizer's actual two-core. -/
theorem innerRadical_le_core : innerRadical ≤ fullNormalizer.pCoreIn 2 :=
  le_pCoreIn_of_normalizes (q₂_isPGroup.map MulAut.conj) innerRadical.le_normalizer le_rfl

/-- The faithful inner embedding restricted to the inner normalizer. -/
def innerNormalizerHom : p₂ →* fullNormalizer :=
  (MulAut.conj.comp p₂.subtype).codRestrict fullNormalizer (by
    intro x
    exact (Subgroup.le_normalizer_map MulAut.conj)
      (mem_map_of_mem MulAut.conj x.property))

/-- Transport the already computed inner residual into the full residual. -/
theorem innerRadical_le_fullResidual : innerRadical ≤ fullResidual := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := q₂_le_innerResidual hx
  exact ⟨innerNormalizerHom y,
    map_pResidual_le 2 innerNormalizerHom (mem_map_of_mem innerNormalizerHom hy), rfl⟩

/-- The first cubic actor belongs to the full normalizer's two-residual. -/
theorem odd_inner_mem_fullResidual (i : Fin 2) :
    MulAut.conj (oddGenerator i) ∈ fullResidual :=
  ⟨innerNormalizerHom ⟨oddGenerator i, oddGenerator_mem_p₂ i⟩,
    map_pResidual_le 2 innerNormalizerHom
      (mem_map_of_mem innerNormalizerHom (oddGenerator_mem_innerResidual i)), rfl⟩

/-- The center bound survives the literal inner embedding. -/
theorem card_center_innerRadical_le : Nat.card (center innerRadical) ≤ 4 := by
  have h := Nat.card_congr (centerCongr
    (q₂.equivMapOfInjective MulAut.conj inner_conj_injective)).toEquiv
  exact h ▸ card_center_q₂_le

end Sporadic.LeechRelated.J2.ExceptionalParabolics.NormalizerAction
