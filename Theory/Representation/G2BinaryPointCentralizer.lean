module

public import Theory.Representation.G2BinaryPointImage
public import Theory.Representation.G2BinaryPointElementary
public import Theory.Representation.G2NaturalTransitivity
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.InvolutionCentralizer
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.FullElementaryEight

/-!
# Self-centralization of binary G₂ point images

The marked elementary eight contains the distinguished long-root involution.
Its centralizer therefore lies in the first parabolic, where the existing
centralizer calculation gives precisely the elementary eight. A normal
elementary image of order eight in an actual point stabilizer is this marked
subgroup after choosing compatible point coordinates.

Source: Aschbacher--Smith B.4.6(13), used in 3.3.28, printed pp.90,601.
The concrete root model retains the attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup

namespace Atlas.G2.BinaryParabolicPair

/-- The root-defined elementary eight is self-centralizing in full G₂(2). -/
theorem centralizer_elementary_eq :
    centralizer (BinaryCore.elementary : Set (Model (ZMod 2))) =
      BinaryCore.elementary := by
  have hle : centralizer (BinaryCore.elementary : Set (Model (ZMod 2))) ≤
      firstParabolic := by
    rw [← centralizer_z_eq_firstParabolic]
    exact centralizer_le (Set.singleton_subset_iff.mpr BinaryCore.z_mem_elementary)
  exact (inf_eq_right.mpr hle).symm.trans marked_elementary_centralizer_first

end Atlas.G2.BinaryParabolicPair

namespace Atlas.G2.Natural.BinaryPointFlag
variable {D : Type*} [Group D]

/-- An elementary eight normal in the actual marked point stabilizer has
self-centralizing image in full G₂(2). -/
theorem marked_point_eight_selfcentralizing
    (f : D →* Model F) (hrange : commutator (Model F) ≤ f.range)
    (C A : Subgroup D) (hAC : A ≤ C)
    (hn : C ≤ normalizer (A : Set D)) [IsElementaryAbelian 2 A]
    (hC : ∀ a, a ∈ C ↔ Restricted.NaturalCoordinates.action F (f a)
      (Pi.single 0 1) = Pi.single 0 1)
    (hcard : Nat.card (A.map f) = 8) :
    centralizer (A.map f : Set (Model F)) = A.map f := by
  obtain ⟨hu, hn'⟩ := marked_point_actor_bounds f hrange C A hAC hn hC
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have he : A.map f = BinaryCore.elementary := eq_of_le_of_card_ge
    (elementary_normalized_point_le (A.map f) hu hn')
    (by rw [hcard, BinaryCore.card_elementary])
  rw [he]
  exact BinaryParabolicPair.centralizer_elementary_eq

/-- The same result for any nonzero natural point, allowing a kernel in the
original actor. This is the form used by local subgroup actions. -/
theorem point_eight_selfcentralizing
    (f : D →* Model F) (hrange : commutator (Model F) ≤ f.range)
    (C A : Subgroup D) (hAC : A ≤ C)
    (hn : C ≤ normalizer (A : Set D)) [IsElementaryAbelian 2 A]
    (v : Natural.Space F) (hv : v ≠ 0)
    (hC : ∀ a, a ∈ C ↔ Natural.action F (f a) v = v)
    (hcard : Nat.card (A.map f) = 8) :
    centralizer (A.map f : Set (Model F)) = A.map f := by
  let E := Restricted.NaturalCoordinates.equiv F
  let z : Natural.Space F := E.symm (Pi.single 0 1)
  have hz : z ≠ 0 := by
    intro h
    have hh : (Pi.single 0 1 : Fin 6 → F) = 0 := by
      simpa only [z, E.apply_symm_apply, map_zero] using congrArg E h
    have hh0 := congrFun hh 0
    simp at hh0
  obtain ⟨g, hg⟩ := Natural.derivedAction_transitive F v z hv hz
  let α := (MulAut.conj (g : Model F)).toMonoidHom
  let f' := α.comp f
  have hrange' : commutator (Model F) ≤ f'.range := by
    intro b hb
    let b' : Model F := (g : Model F)⁻¹ * b * (g : Model F)
    have hb' : b' ∈ commutator (Model F) := by
      have hh := (inferInstance : (commutator (Model F)).Normal).conj_mem
        b hb (g : Model F)⁻¹
      simpa only [inv_inv] using hh
    obtain ⟨a, ha⟩ := hrange hb'
    refine ⟨a, ?_⟩
    change (g : Model F) * f a * (g : Model F)⁻¹ = b
    rw [ha]
    dsimp only [b']
    group
  have hpoint : E (Natural.action F (g : Model F) v) = Pi.single 0 1 := by
    change E (Natural.derivedAction F g v) = _
    rw [hg]
    exact E.apply_symm_apply _
  have hconj (a : D) : Natural.action F (f' a)
      (Natural.action F (g : Model F) v) =
      Natural.action F (g : Model F) (Natural.action F (f a) v) := by
    change Natural.action F ((g : Model F) * f a * (g : Model F)⁻¹)
      (Natural.action F (g : Model F) v) = _
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have hC' (a : D) : a ∈ C ↔ Restricted.NaturalCoordinates.action F (f' a)
      (Pi.single 0 1) = Pi.single 0 1 := by
    rw [← hpoint]
    have hc := LinearMap.congr_fun
      ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' (f' a))
      (Natural.action F (g : Model F) v)
    change E (Natural.action F (f' a) (Natural.action F (g : Model F) v)) =
      Restricted.NaturalCoordinates.action F (f' a)
        (E (Natural.action F (g : Model F) v)) at hc
    rw [← hc, E.injective.eq_iff, hconj,
      ((Natural.action F).apply_bijective (g : Model F)).1.eq_iff]
    exact hC a
  have hmap : (A.map f).map α = A.map f' := map_map _ _ _
  have hcard' : Nat.card (A.map f') = 8 := by
    rw [← hmap, card_map_of_injective (MulAut.conj (g : Model F)).injective]
    exact hcard
  have hself := marked_point_eight_selfcentralizing f' hrange' C A hAC hn hC' hcard'
  apply le_antisymm
  · intro x hx
    have hx' : α x ∈ centralizer (A.map f' : Set (Model F)) := by
      rw [← hmap]
      exact map_centralizer_le_centralizer_image _ α (mem_map_of_mem α hx)
    rw [hself, ← hmap] at hx'
    obtain ⟨y, hy, he⟩ := hx'
    exact (MulAut.conj (g : Model F)).injective he ▸ hy
  · let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
    intro x hx y hy
    exact congrArg Subtype.val
      ((inferInstance : IsMulCommutative (A.map f)).is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)

end Atlas.G2.Natural.BinaryPointFlag
