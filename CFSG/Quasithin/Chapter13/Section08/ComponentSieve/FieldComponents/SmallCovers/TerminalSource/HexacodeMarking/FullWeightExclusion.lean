module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.ThreeDimensional
public import Theory.Representation.HexacodeAction.PlaneStabilizer.TwoCore
public import Theory.GroupTheory.SylowKernelCore

/-!
# Excluding full-weight points with an intrinsic two-core of order four

The image of the literal point stabilizer is the intersection of the actor
image with the binary subspace stabilizer. Its intrinsic two-core is the
image of the original two-core under the faithful embedding. The scalar lies
in this image stabilizer, so its two-core lies in the even hexacode group.
The full even plane stabilizer is contained in the image stabilizer, hence
normalizes that two-core. The model calculation then excludes order four.

This supplies the full-weight orbit exclusion in the intrinsic marking for
the alternative-section repair of Aschbacher–Smith 13.8.21(2), printed p.956
(PDF p.973), combined manuscript of 1 March 2004. The geometric dichotomy
and the pair-core lift calculation belong to the marking assembly. No
stabilizer kernel identity or coordinate-pair selection is assumed here.
The full-weight hypothesis already includes the binary dimension and scalar
stability, so this exclusion needs no additional field-dimension hypothesis.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking
open Atlas.Codes Subgroup Representation.Hexacode

variable {A : Type*} [Group A]

/-- A full-weight field point cannot have an intrinsic two-core of order four. -/
theorem fullWeight_twoCore_card_ne_four (e : A →* HexAutomorphisms)
    (he : Function.Injective e) (heven : hexSign.ker ≤ e.range)
    (D : Submodule F hexacode)
    (hD : IsFullWeightScalarPlane (D.restrictScalars (ZMod 2))) :
    Nat.card ((pointStabilizer e D).pCoreIn 2) ≠ 4 := by
  intro hfour
  let S := Representation.BinaryOffender.subspaceStabilizer action (D.restrictScalars (ZMod 2))
  let H := (pointStabilizer e D).map e
  have hH : H = S ⊓ e.range := (Subgroup.map_comap_eq e S).trans (inf_comm _ _)
  let Q := H.pCoreIn 2
  have hQmap : Q = ((pointStabilizer e D).pCoreIn 2).map e :=
    (Subgroup.map_pCoreIn_of_injective 2 (pointStabilizer e D) e he).symm
  have hQcard : Nat.card Q = 4 := by
    rw [hQmap, Subgroup.card_map_of_injective he, hfour]
  have hz : hexZ ∈ H := by
    rw [hH]
    exact ⟨hD.2.1, heven hexSign_Z⟩
  have hQeven : Q ≤ hexSign.ker := twoCore_le_even_of_scalar_mem H hz
  let E := hexSign.ker ⊓ S
  have hEH : E ≤ H := by
    rw [hH]
    exact le_inf inf_le_right (inf_le_left.trans heven)
  have hQE : Q ≤ E := le_inf hQeven ((pCoreIn_le 2 H).trans (hH ▸ inf_le_left))
  have hHnorm : H ≤ normalizer (Q : Set HexAutomorphisms) := by
    have h := Subgroup.le_normalizer_map (H := pCore 2 H) H.subtype
    rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype] at h
    exact h
  let N := Q.subgroupOf E
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hQE).mpr (hEH.trans hHnorm)
  apply fullWeightScalarPlaneStabilizer_normal_card_ne_four _ hD N
  exact (Nat.card_congr (subgroupOfEquivOfLe hQE).toEquiv).trans hQcard

/-- The order-four hypothesis selects the non-full-weight branch of the geometric dichotomy. -/
theorem not_fullWeight_of_twoCore_card_eq_four (e : A →* HexAutomorphisms)
    (he : Function.Injective e) (heven : hexSign.ker ≤ e.range)
    (D : Submodule F hexacode) (hfour : Nat.card ((pointStabilizer e D).pCoreIn 2) = 4) :
    ¬ IsFullWeightScalarPlane (D.restrictScalars (ZMod 2)) := by
  intro hD
  exact fullWeight_twoCore_card_ne_four e he heven D hD hfour

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking
