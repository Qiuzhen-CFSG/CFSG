module

public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.Membership

/-! Finite normalizer enumeration, adapted from
`Stellmacher.SectionNine.NineFiveM12NormalizerEnumeration`.
The coordinates encode the orbits and point stabilizers of the marked natural four. -/

@[expose] public section

namespace Sporadic.Mathieu.M12SmallPair.SylowEnumeration

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev NormalizerPoint := Fin 3 × Fin 2 × Fin 2

def normalizerPointEquiv : NormalizerPoint ≃ Fin 12 where
  toFun point := ![![![1, 5], ![6, 8]], ![![3, 4], ![10, 11]],
    ![![2, 0], ![7, 9]]] point.1 point.2.1 point.2.2
  invFun point := ![(2, 0, 1), (0, 0, 0), (2, 0, 0), (1, 0, 0),
    (1, 0, 1), (0, 0, 1), (0, 1, 0), (2, 1, 0),
    (0, 1, 1), (2, 1, 1), (1, 1, 0), (1, 1, 1)] point
  left_inv := by decide +kernel
  right_inv := by decide +kernel

abbrev NormalizerParameters := Equiv.Perm (Fin 3) ×
  (Fin 3 → Equiv.Perm (Fin 2)) × (Fin 3 × Fin 2 → Equiv.Perm (Fin 2))

def normalizerCoordinatePerm (parameters : NormalizerParameters) :
    Equiv.Perm NormalizerPoint :=
  (Equiv.prodCongrRight (fun classIndex =>
    (Equiv.prodCongrRight (fun orbitIndex => parameters.2.2 (classIndex, orbitIndex))).trans
      (Equiv.prodCongr (parameters.2.1 classIndex) (Equiv.refl _)))).trans
    (Equiv.prodCongr parameters.1 (Equiv.refl _))

theorem normalizerCoordinatePerm_apply (parameters : NormalizerParameters)
    (point : NormalizerPoint) :
    normalizerCoordinatePerm parameters point =
      (parameters.1 point.1, parameters.2.1 point.1 point.2.1,
        parameters.2.2 (point.1, point.2.1) point.2.2) := rfl

theorem normalizerCoordinatePerm_injective :
    Function.Injective normalizerCoordinatePerm := by
  rintro ⟨firstClass, firstOrbit, firstEnd⟩ ⟨secondClass, secondOrbit, secondEnd⟩ heq
  have hclass : firstClass = secondClass := by
    apply Equiv.ext
    intro classIndex
    exact congrArg (fun permutation => (permutation (classIndex, 0, 0)).1) heq
  have horbit : firstOrbit = secondOrbit := by
    funext classIndex
    apply Equiv.ext
    intro orbitIndex
    exact congrArg (fun permutation => (permutation (classIndex, orbitIndex, 0)).2.1) heq
  have hend : firstEnd = secondEnd := by
    funext point
    apply Equiv.ext
    intro endpoint
    exact congrArg (fun permutation => (permutation (point.1, point.2, endpoint)).2.2) heq
  simp only [hclass, horbit, hend]

def normalizerParameterPerm (parameters : NormalizerParameters) : Equiv.Perm (Fin 12) :=
  normalizerPointEquiv.permCongr (normalizerCoordinatePerm parameters)

theorem normalizerParameterPerm_injective : Function.Injective normalizerParameterPerm :=
  normalizerPointEquiv.permCongr.injective.comp normalizerCoordinatePerm_injective

def normalizerParameterEmbedding : NormalizerParameters ↪ Equiv.Perm (Fin 12) :=
  ⟨normalizerParameterPerm, normalizerParameterPerm_injective⟩

def normalizerSymmetricCarrier : Finset (Equiv.Perm (Fin 12)) :=
  Finset.univ.map normalizerParameterEmbedding

theorem normalizerSymmetricCarrier_card : normalizerSymmetricCarrier.card = 3072 := by
  rw [normalizerSymmetricCarrier, Finset.card_map]
  decide +kernel

end Sporadic.Mathieu.M12SmallPair.SylowEnumeration
