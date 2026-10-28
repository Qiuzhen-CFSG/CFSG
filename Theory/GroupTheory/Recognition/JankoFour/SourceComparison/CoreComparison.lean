module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerActions
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeStabilizers

/-!
# Compatible six-cover and quadratic core coordinates

Compose the original six-cover with the actual triple-cover coordinates used
by the native core module. Equal-degree cover comparison over M₂₂ and
perfectness lift the comparison to these same triple-cover coordinates.
The full H/Q action and the quadratic space Q/Z(Q) are then compared using
the existing native representation. Their compatibility on the six-cover
is proved through the literal quotient maps.

This is the cover/module compatibility step in AS91 (8.3), p.606. Lifting
the quadratic comparison to the extraspecial groups and gluing the full H
remain further obligations; no group comparison is assumed here.
-/

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu PerfectCentralCovering

variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))

/-- The genuine triple cover map on the original six-cover, in the same
marking used by the native core module. -/
noncomputable def cubicNativeProjection : cubicCentralizerInH e X →* M22TripleCover :=
  (innerPreimageTripleEquiv h e).toMonoidHom.comp (cubicCentralizerToInner h e X)

theorem cubicNativeProjection_surjective : Function.Surjective (cubicNativeProjection h e X) :=
  (innerPreimageTripleEquiv h e).surjective.comp (cubicCentralizerToInner_surjective h e X)

theorem cubicNativeProjection_ker :
    (cubicNativeProjection h e X).ker =
      (center (centralizer z)).subgroupOf (cubicCentralizerInH e X) := by
  rw [cubicNativeProjection,MonoidHom.ker_comp_of_injective _ _
    (innerPreimageTripleEquiv h e).injective,cubicCentralizerToInner_ker]

theorem cubicNativeProjection_ker_central :
    (cubicNativeProjection h e X).ker ≤ center (cubicCentralizerInH e X) := by
  rw [cubicNativeProjection_ker]
  intro c hc
  apply mem_center_iff.mpr
  intro d
  exact Subtype.ext (mem_center_iff.mp hc d.val)

noncomputable def cubicNativeCover (hp : Group.IsPerfect (cubicCentralizerInH e X)) :
    Cover (cubicCentralizerInH e X) M22TripleCover where
  toMonoidHom := cubicNativeProjection h e X
  surjective := cubicNativeProjection_surjective h e X
  ker_le_center := cubicNativeProjection_ker_central h e X
  isPerfect := hp

/-- Compose with the native triple-cover quotient, keeping the same module marking. -/
noncomputable def cubicNativeSimpleCover (hp : Group.IsPerfect (cubicCentralizerInH e X)) :
    Cover (cubicCentralizerInH e X) M22 where
  toMonoidHom := (M22TripleCover.coverOfCentralQuotientEquiv M22TripleCover.centralQuotientEquiv).toMonoidHom.comp
    (cubicNativeProjection h e X)
  surjective := (M22TripleCover.coverOfCentralQuotientEquiv M22TripleCover.centralQuotientEquiv).surjective.comp
    (cubicNativeProjection_surjective h e X)
  isPerfect := hp
  ker_le_center := by
    rw [← MonoidHom.comap_ker,M22TripleCover.coverOfCentralQuotientEquiv_ker]
    exact (cubicNativeCover h e X hp).comap_center.le

variable (hp : Group.IsPerfect (cubicCentralizerInH e X))

theorem cubicNativeSimpleCover_ker :
    (cubicNativeSimpleCover h e X hp).toMonoidHom.ker = center (cubicCentralizerInH e X) := by
  change ((M22TripleCover.coverOfCentralQuotientEquiv M22TripleCover.centralQuotientEquiv).toMonoidHom.comp
    (cubicNativeProjection h e X)).ker = _
  rw [← MonoidHom.comap_ker,M22TripleCover.coverOfCentralQuotientEquiv_ker]
  exact (cubicNativeCover h e X hp).comap_center

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))
variable (hp' : Group.IsPerfect (cubicCentralizerInH e' X'))

include hp hp' in
/-- Align the actual six-cover with the triple-cover coordinates of the core
module, not just with an independently selected simple quotient marking. -/
theorem exists_cubicCentralizer_equiv_native :
    ∃ φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X',
      (∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c) ∧
      ((cubicSylowImage e X).subgroupOf (cubicCentralizerInH e X)).map φ.toMonoidHom =
        (cubicSylowImage e' X').subgroupOf (cubicCentralizerInH e' X') ∧
      φ (cubicMarker e X) = cubicMarker e' X' := by
  obtain ⟨φ,hφ⟩ := exists_m22_cover_equiv_over
    (cubicNativeSimpleCover h e X hp) (cubicNativeSimpleCover h' e' X' hp') (by
      rw [cubicNativeSimpleCover_ker,cubicNativeSimpleCover_ker,
        cubicCentralizer_center_card h e X hp,cubicCentralizer_center_card h' e' X' hp'])
  let := hp
  have he : (cubicNativeProjection h' e' X').comp φ.toMonoidHom = cubicNativeProjection h e X := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq
      (M22TripleCover.coverOfCentralQuotientEquiv M22TripleCover.centralQuotientEquiv).toMonoidHom
      (M22TripleCover.coverOfCentralQuotientEquiv M22TripleCover.centralQuotientEquiv).ker_le_center
    apply MonoidHom.ext
    exact hφ
  exact ⟨φ,DFunLike.congr_fun he,cubicCentralizerEquiv_scalar h e X hp h' e' X' hp' φ,
    cubicCentralizerEquiv_marker h e X h' e' X' hp' φ⟩

variable [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')]

/-- Comparison of the full quotient actions in the same native coordinates. -/
noncomputable def coreQuotientComparison :
    (centralizer z ⧸ core z) ≃* (centralizer z' ⧸ core z') :=
  (coreAmbientEquiv h e X).trans (coreAmbientEquiv h' e' X').symm

/-- Comparison of the underlying quadratic spaces in those same coordinates. -/
noncomputable def coreSpaceComparison : CoreSpace (z := z) ≃ₗ[ZMod 2] CoreSpace (z := z') :=
  (coreNativeEquiv h e X).trans (coreNativeEquiv h' e' X').symm

theorem coreSpaceComparison_quadratic (v : CoreSpace (z := z)) :
    coreQuadraticForm (coreSpaceComparison h e X h' e' X' v) = coreQuadraticForm v := by
  rw [← coreNativeEquiv_quadratic h' e' X',← coreNativeEquiv_quadratic h e X]
  change M22TripleCover.Unitary.quadraticForm ((coreNativeEquiv h' e' X') ((coreNativeEquiv h' e' X').symm
    (coreNativeEquiv h e X v))) = _
  rw [LinearEquiv.apply_symm_apply]

theorem coreSpaceComparison_intertwines (g : centralizer z ⧸ core z) (v : CoreSpace (z := z)) :
    coreSpaceComparison h e X h' e' X' (coreBinaryRepresentation h g v) =
      coreBinaryRepresentation h' (coreQuotientComparison h e X h' e' X' g)
        (coreSpaceComparison h e X h' e' X' v) := by
  apply (coreNativeEquiv h' e' X').injective
  change coreNativeEquiv h' e' X' ((coreNativeEquiv h' e' X').symm
    (coreNativeEquiv h e X (coreBinaryRepresentation h g v))) = _
  rw [LinearEquiv.apply_symm_apply,coreAmbientHom_intertwines,coreAmbientHom_intertwines]
  have hg : coreAmbientHom h' e' X' (coreQuotientComparison h e X h' e' X' g) =
      coreAmbientHom h e X g := (coreAmbientEquiv h' e' X').apply_symm_apply _
  rw [hg]
  congr 1
  change coreNativeEquiv h e X v = ((coreNativeEquiv h' e' X') ((coreNativeEquiv h' e' X').symm
    (coreNativeEquiv h e X v)))
  rw [LinearEquiv.apply_symm_apply]

/-- The cover and module comparisons agree already in the literal H/Q. -/
theorem cubicNativeComparison_core
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (hφ : ∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c)
    (c : cubicCentralizerInH e X) :
    QuotientGroup.mk' (core z') (φ c).val =
      coreQuotientComparison h e X h' e' X' (QuotientGroup.mk' (core z) c.val) := by
  apply (coreAmbientEquiv h' e' X').injective
  change coreAmbientHom h' e' X' (cubicCentralizerToInner h' e' X' (φ c)).val =
    coreAmbientEquiv h' e' X' ((coreAmbientEquiv h' e' X').symm
      (coreAmbientEquiv h e X (cubicCentralizerToInner h e X c).val))
  rw [MulEquiv.apply_symm_apply]
  change coreAmbientHom h' e' X' (cubicCentralizerToInner h' e' X' (φ c)).val =
    coreAmbientHom h e X (cubicCentralizerToInner h e X c).val
  rw [coreAmbientHom_on_inner,coreAmbientHom_on_inner]
  exact congrArg Janko4.InvolutionCentralizers.First.QuotientExtension.coverInclusion (hφ c)

include hp hp' in
/-- Simultaneous cover and core comparison, with the same literal conjugation
actors and quadratic forms. No independent equivalence is assumed. -/
theorem exists_cubicCentralizer_equiv_core :
    ∃ φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X',
      (∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c) ∧
      φ (cubicMarker e X) = cubicMarker e' X' ∧
      (∀ c, QuotientGroup.mk' (core z') (φ c).val =
        coreQuotientComparison h e X h' e' X' (QuotientGroup.mk' (core z) c.val)) ∧
      (∀ c v, coreSpaceComparison h e X h' e' X'
        (coreBinaryRepresentation h (QuotientGroup.mk' (core z) c.val) v) =
          coreBinaryRepresentation h' (QuotientGroup.mk' (core z') (φ c).val)
            (coreSpaceComparison h e X h' e' X' v)) := by
  obtain ⟨φ,hφ,_,hz⟩ := exists_cubicCentralizer_equiv_native h e X hp h' e' X' hp'
  have hc := cubicNativeComparison_core h e X h' e' X' φ hφ
  refine ⟨φ,hφ,hz,hc,?_⟩
  intro c v
  rw [hc]
  exact coreSpaceComparison_intertwines h e X h' e' X' _ v

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
