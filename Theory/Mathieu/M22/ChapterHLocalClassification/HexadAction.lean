module

public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.Restriction
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.InvariantForm
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.SymplecticComparison

/-!
# The natural conjugation modules of the two native hexad kernels

The inner and outer kernels inherit the same binary four-space from the native
octad kernel. The preserved nondegenerate alternating form identifies the outer
action with Sp₄(2); the concrete polar comparison identifies it with the natural
six-letter module. Its A₆ restriction gives the inner action. All invariant-form
and model-comparison premises are discharged here.

`Natural.outerMarking` explicitly composes the original six-coordinate quotient
equivalence, its relabeling, and `Natural.markingAutomorphism`. The inner marking
uses the restriction of that same automorphism. The original coordinate markings
are preserved. The natural module is the four-dimensional deleted permutation
module, not the five-dimensional deleted cocode.

The conjugation equations use both the intrinsic two-cores with their relative
normality and their actual ambient images. The maps and coordinates agree under
the literal native M22 inclusion in its setwise-pair overgroup. The outer map's
kernel coordinates also have the convention required by the subsequent offender
arguments; its quintet and Sylow image markings are separate obligations.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, H.14.3(3),
printed p.397 (PDF p.408), deduced from the native octad action H.14.1(4).
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.Hexad.CocodeAction.SixPointModel
namespace Sporadic.Mathieu.M22ChapterH.Hexad.Action
noncomputable section

/-- Coordinates on the intrinsic inner core, before mapping it into M22. -/
def innerCoreCoordinates : pCore 2 Inner ≃* Multiplicative Space :=
  ((pCore 2 Inner).equivMapOfInjective Inner.subtype Inner.subtype_injective).trans
    innerCoordinates

/-- Coordinates on the intrinsic outer core, before mapping it into the pair group. -/
def outerCoreCoordinates : pCore 2 Outer ≃* Multiplicative Space :=
  ((pCore 2 Outer).equivMapOfInjective Outer.subtype Outer.subtype_injective).trans
    outerCoordinates

/-- Conjugation uses normality inside the inner hexad stabilizer. -/
theorem innerCoreCoordinates_conjugation (g : Inner) (a : pCore 2 Inner) :
    (innerCoreCoordinates
      ⟨g * a.val * g⁻¹, (inferInstance : (pCore 2 Inner).Normal).conj_mem a.val a.property g⟩).toAdd =
      alternatingAction (innerQuotientEquiv (QuotientGroup.mk g))
        (innerCoreCoordinates a).toAdd := by
  rw [alternatingAction_mk]
  apply congrArg Multiplicative.toAdd
  change innerCoordinates _ = Multiplicative.ofAdd _
  apply innerCoordinates.symm.injective
  erw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  change g.val * a.val.val * g.val⁻¹ = _
  have h := innerCoordinates_conjugation g (innerCoreCoordinates a).toAdd
  have ha : (innerCoordinates.symm (innerCoreCoordinates a)).val = a.val.val := by
    change (innerCoordinates.symm (innerCoordinates _)).val = _
    erw [MulEquiv.symm_apply_apply]
    rfl
  exact ha ▸ h

/-- The literal intrinsic outer conjugation equation for the original S6 marking. -/
theorem outerCoreCoordinates_conjugation (g : Outer) (a : pCore 2 Outer) :
    (outerCoreCoordinates
      ⟨g * a.val * g⁻¹, (inferInstance : (pCore 2 Outer).Normal).conj_mem a.val a.property g⟩).toAdd =
      symmetricAction (outerQuotientEquiv (QuotientGroup.mk g))
        (outerCoreCoordinates a).toAdd := by
  rw [outerQuotientEquiv_mk, symmetricAction_coordinate]
  apply congrArg Multiplicative.toAdd
  change outerCoordinates _ = Multiplicative.ofAdd _
  apply outerCoordinates.symm.injective
  erw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  change g.val * a.val.val * g.val⁻¹ = _
  have h := outerCoordinates_conjugation g (outerCoreCoordinates a).toAdd
  have ha : (outerCoordinates.symm (outerCoreCoordinates a)).val = a.val.val := by
    change (outerCoordinates.symm (outerCoordinates _)).val = _
    erw [MulEquiv.symm_apply_apply]
    rfl
  exact ha ▸ h

/-- The actual S6 action has full order 720. -/
theorem symmetricAction_range_card : Nat.card symmetricAction.range = 720 := by
  calc
    _ = Nat.card (Equiv.Perm H) :=
      (Nat.card_congr (Equiv.ofInjective symmetricAction symmetricAction_injective)).symm
    _ = 720 := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, card_H]; decide

/-- Its compatible A6 restriction has order 360. -/
theorem alternatingAction_range_card : Nat.card alternatingAction.range = 360 := by
  have : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_eq_fintype_card, card_H]; decide)
  calc
    _ = Nat.card (alternatingGroup H) :=
      (Nat.card_congr (Equiv.ofInjective alternatingAction alternatingAction_injective)).symm
    _ = 360 := by rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, card_H]; decide


namespace Natural

/-- The automorphism comparing the original six-coordinate action with the natural model. -/
def markingAutomorphism : Equiv.Perm (Fin 6) ≃* Equiv.Perm (Fin 6) :=
  SymplecticComparison.markingAutomorphism invariantForm invariantForm_isAlt
    invariantForm_nondegenerate invariantForm_symmetric

/-- The inherited octad four-space in natural six-letter module coordinates. -/
def spaceCoordinates : Space ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
  SymplecticComparison.naturalCoordinates invariantForm invariantForm_isAlt
    invariantForm_nondegenerate

/-- The natural outer marking, after the explicit comparison automorphism. -/
def outerMarking : (Outer ⧸ pCore 2 Outer) ≃* Equiv.Perm (Fin 6) :=
  SymplecticComparison.outerNaturalMarking invariantForm invariantForm_isAlt
    invariantForm_nondegenerate invariantForm_symmetric

/-- The compatible natural inner marking, using the restriction of the same automorphism. -/
def innerMarking : (Inner ⧸ pCore 2 Inner) ≃* alternatingGroup (Fin 6) :=
  SymplecticComparison.innerNaturalMarking invariantForm invariantForm_isAlt
    invariantForm_nondegenerate invariantForm_symmetric

theorem outerMarking_apply (q : Outer ⧸ pCore 2 Outer) :
    outerMarking q = markingAutomorphism
      (SymplecticComparison.sixRelabeling.permCongrHom (outerQuotientEquiv q)) := rfl

theorem innerMarking_coe (q : Inner ⧸ pCore 2 Inner) :
    (innerMarking q).val = markingAutomorphism
      (SymplecticComparison.sixRelabeling.permCongrHom (innerQuotientEquiv q).val) :=
  SymplecticComparison.innerNaturalMarking_coe invariantForm invariantForm_isAlt
    invariantForm_nondegenerate invariantForm_symmetric q

theorem markingAutomorphism_preserves_alternating :
    (alternatingGroup (Fin 6)).map markingAutomorphism.toMonoidHom =
      alternatingGroup (Fin 6) :=
  HexadSymplecticComparison.automorphism_map_alternating _

/-- The original S6(H) action becomes natural only after the displayed change of marking. -/
theorem symmetricAction_natural (s : Equiv.Perm H) (v : Space) :
    spaceCoordinates (symmetricAction s v) =
      BinaryPermutation.naturalRepresentation (Fin 6)
        (markingAutomorphism (SymplecticComparison.sixRelabeling.permCongrHom s))
        (spaceCoordinates v) :=
  SymplecticComparison.symmetricAction_natural invariantForm invariantForm_isAlt
    invariantForm_nondegenerate invariantForm_symmetric s v

theorem outerQuotientAction_natural (q : Outer ⧸ pCore 2 Outer) (v : Space) :
    spaceCoordinates (outerQuotientAction q v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (outerMarking q) (spaceCoordinates v) :=
  SymplecticComparison.outerQuotientAction_natural invariantForm invariantForm_isAlt
    invariantForm_nondegenerate invariantForm_symmetric q v

theorem innerQuotientAction_natural (q : Inner ⧸ pCore 2 Inner) (v : Space) :
    spaceCoordinates (innerQuotientAction q v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (innerMarking q).val (spaceCoordinates v) :=
  SymplecticComparison.innerQuotientAction_natural invariantForm invariantForm_isAlt
    invariantForm_nondegenerate invariantForm_symmetric q v

/-- The surjective natural quotient map on the literal pair-overgroup stabilizer. -/
def outerMap : Outer →* Equiv.Perm (Fin 6) :=
  outerMarking.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Outer))

/-- The corresponding natural quotient map on the native M22 stabilizer. -/
def innerMap : Inner →* alternatingGroup (Fin 6) :=
  innerMarking.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Inner))

theorem outerMap_coordinate (g : Outer) :
    outerMap g = markingAutomorphism
      (SymplecticComparison.sixRelabeling.permCongrHom (outerCoordinateAction g)) := by
  change outerMarking (QuotientGroup.mk g) = _
  rw [outerMarking_apply, outerQuotientEquiv_mk]

theorem innerMap_coordinate (g : Inner) :
    (innerMap g).val = markingAutomorphism
      (SymplecticComparison.sixRelabeling.permCongrHom (innerCoordinateAction g)) := by
  change (innerMarking (QuotientGroup.mk g)).val = _
  rw [innerMarking_coe, innerQuotientEquiv_mk]

theorem outerMap_surjective : Function.Surjective outerMap :=
  outerMarking.surjective.comp (QuotientGroup.mk'_surjective _)

theorem innerMap_surjective : Function.Surjective innerMap :=
  innerMarking.surjective.comp (QuotientGroup.mk'_surjective _)

theorem outerMap_ker : outerMap.ker = pCore 2 Outer := by
  ext g
  change outerMarking (QuotientGroup.mk g) = 1 ↔ _
  rw [map_eq_one_iff _ outerMarking.injective, QuotientGroup.eq_one_iff]

theorem innerMap_ker : innerMap.ker = pCore 2 Inner := by
  ext g
  change innerMarking (QuotientGroup.mk g) = 1 ↔ _
  rw [map_eq_one_iff _ innerMarking.injective, QuotientGroup.eq_one_iff]

/-- Both natural markings respect the literal inclusion M22 → pair stabilizer. -/
theorem maps_compatible (g : Inner) : outerMap (innerToOuter g) = (innerMap g).val :=
  SymplecticComparison.naturalMarkings_compatible invariantForm invariantForm_isAlt
    invariantForm_nondegenerate invariantForm_symmetric g

theorem outerLinearAction_natural (g : Outer) (v : Space) :
    spaceCoordinates (outerLinearAction g v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (outerMap g) (spaceCoordinates v) :=
  outerQuotientAction_natural (QuotientGroup.mk g) v

theorem innerLinearAction_natural (g : Inner) (v : Space) :
    spaceCoordinates (innerLinearAction g v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (innerMap g).val (spaceCoordinates v) :=
  innerQuotientAction_natural (QuotientGroup.mk g) v

/-- Natural coordinates on the intrinsic outer two-core. -/
def outerCore : pCore 2 Outer ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  outerCoreCoordinates.trans spaceCoordinates.toAddEquiv.toMultiplicative

/-- Natural coordinates on the intrinsic inner two-core. -/
def innerCore : pCore 2 Inner ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  innerCoreCoordinates.trans spaceCoordinates.toAddEquiv.toMultiplicative

/-- H.14.3(3) for the actual outer stabilizer and its relative two-core. -/
theorem outerCore_conjugation (g : Outer) (a : pCore 2 Outer) :
    (outerCore
      ⟨g * a.val * g⁻¹, (inferInstance : (pCore 2 Outer).Normal).conj_mem a.val a.property g⟩).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (outerMap g) (outerCore a).toAdd := by
  change spaceCoordinates (outerCoreCoordinates _).toAdd = _
  rw [outerCoreCoordinates_conjugation, outerQuotientEquiv_mk, symmetricAction_coordinate]
  exact outerLinearAction_natural g (outerCoreCoordinates a).toAdd

/-- H.14.3(3) for the actual inner stabilizer and its relative two-core. -/
theorem innerCore_conjugation (g : Inner) (a : pCore 2 Inner) :
    (innerCore
      ⟨g * a.val * g⁻¹, (inferInstance : (pCore 2 Inner).Normal).conj_mem a.val a.property g⟩).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (innerMap g).val (innerCore a).toAdd := by
  change spaceCoordinates (innerCoreCoordinates _).toAdd = _
  rw [innerCoreCoordinates_conjugation, alternatingAction_mk]
  exact innerLinearAction_natural g (innerCoreCoordinates a).toAdd

/-- Natural coordinates on the kernel as an actual subgroup of the pair overgroup. -/
def outerKernel : m22OuterHexadKernel O ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  outerCoordinates.trans spaceCoordinates.toAddEquiv.toMultiplicative

/-- Natural coordinates on the kernel as an actual subgroup of native M22. -/
def innerKernel : m22InnerHexadKernel O ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  innerCoordinates.trans spaceCoordinates.toAddEquiv.toMultiplicative

theorem kernels_compatible (a : m22InnerHexadKernel O) :
    outerKernel (kernelToOuter a) = innerKernel a :=
  congrArg spaceCoordinates.toAddEquiv.toMultiplicative (coordinates_compatible a)

private theorem outerKernel_symm_apply (v : BinaryPermutation.natural (Fin 6)) :
    outerKernel.symm (Multiplicative.ofAdd v) =
      outerCoordinates.symm (Multiplicative.ofAdd (spaceCoordinates.symm v)) := rfl

private theorem innerKernel_symm_apply (v : BinaryPermutation.natural (Fin 6)) :
    innerKernel.symm (Multiplicative.ofAdd v) =
      innerCoordinates.symm (Multiplicative.ofAdd (spaceCoordinates.symm v)) := rfl

/-- The literal ambient conjugation equation in the pair overgroup. -/
theorem outerKernel_conjugation (g : Outer) (v : BinaryPermutation.natural (Fin 6)) :
    g.val * (outerKernel.symm (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (outerKernel.symm (Multiplicative.ofAdd
        (BinaryPermutation.naturalRepresentation (Fin 6) (outerMap g) v))).val := by
  have he := outerLinearAction_natural g (spaceCoordinates.symm v)
  rw [LinearEquiv.apply_symm_apply] at he
  have hv := congrArg spaceCoordinates.symm he
  rw [LinearEquiv.symm_apply_apply] at hv
  rw [outerKernel_symm_apply, outerKernel_symm_apply, outerCoordinates_conjugation, hv]

/-- The literal ambient conjugation equation in native M22. -/
theorem innerKernel_conjugation (g : Inner) (v : BinaryPermutation.natural (Fin 6)) :
    g.val * (innerKernel.symm (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (innerKernel.symm (Multiplicative.ofAdd
        (BinaryPermutation.naturalRepresentation (Fin 6) (innerMap g).val v))).val := by
  have he := innerLinearAction_natural g (spaceCoordinates.symm v)
  rw [LinearEquiv.apply_symm_apply] at he
  have hv := congrArg spaceCoordinates.symm he
  rw [LinearEquiv.symm_apply_apply] at hv
  rw [innerKernel_symm_apply, innerKernel_symm_apply, innerCoordinates_conjugation, hv]

/-- The map kernel is also the relative subgroup of the actual ambient hexad kernel. -/
theorem outerMap_ker_subgroupOf :
    outerMap.ker = (m22OuterHexadKernel O).subgroupOf Outer := by
  rw [outerMap_ker]
  exact (Subgroup.comap_map_eq_self_of_injective Outer.subtype_injective (pCore 2 Outer)).symm

private theorem outerMap_ker_le_inner : outerMap.ker ≤ innerToOuter.range := by
  intro g hg
  have hk : g.val ∈ m22OuterHexadKernel O := by
    exact (show g ∈ (m22OuterHexadKernel O).subgroupOf Outer from
      outerMap_ker_subgroupOf ▸ hg)
  rw [← inner_kernel_map_pair] at hk
  obtain ⟨a, ha, he⟩ := hk
  obtain ⟨b, hb, rfl⟩ := ha
  exact ⟨b, Subtype.ext he⟩

private theorem innerToOuter_range_map :
    innerToOuter.range.map outerMap = alternatingGroup (Fin 6) := by
  ext s
  constructor
  · rintro ⟨g, ⟨a, rfl⟩, rfl⟩
    rw [maps_compatible]
    exact (innerMap a).property
  · intro hs
    obtain ⟨a, ha⟩ := innerMap_surjective ⟨s, hs⟩
    exact ⟨innerToOuter a, ⟨a, rfl⟩, (maps_compatible a).trans (congrArg Subtype.val ha)⟩

/-- The even preimage is exactly the native inner subgroup inside the hexad stabilizer. -/
theorem outerMap_inner_preimage :
    (alternatingGroup (Fin 6)).comap outerMap =
      m22ToPairStabilizer.range.subgroupOf Outer := by
  rw [← innerToOuter_range_map, Subgroup.comap_map_eq_self outerMap_ker_le_inner]
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, rfl⟩
  · rintro ⟨a, ha⟩
    have hp : a ∈ Inner := by
      change m22ToPairStabilizer a ∈ Outer
      rw [ha]
      exact g.property
    exact ⟨⟨a, hp⟩, Subtype.ext ha⟩

/-- The coordinates in the exact map-kernel convention used by downstream offender arguments. -/
def outerMapCoordinates : outerMap.ker ≃ BinaryPermutation.natural (Fin 6) :=
  ((MulEquiv.subgroupCongr outerMap_ker).trans outerCore).toEquiv.trans Multiplicative.toAdd

theorem outerMapCoordinates_mul (a b : outerMap.ker) :
    outerMapCoordinates (a * b) = outerMapCoordinates a + outerMapCoordinates b :=
  congrArg Multiplicative.toAdd (((MulEquiv.subgroupCongr outerMap_ker).trans outerCore).map_mul a b)

/-- The natural-action field of HexadQuotientData, with no natural-action premise. -/
theorem outerMapCoordinates_conjugation (g : Outer) (a : outerMap.ker) :
    outerMapCoordinates
      ⟨g * a.val * g⁻¹, (inferInstance : outerMap.ker.Normal).conj_mem a.val a.property g⟩ =
      BinaryPermutation.naturalRepresentation (Fin 6) (outerMap g) (outerMapCoordinates a) :=
  outerCore_conjugation g ((MulEquiv.subgroupCongr outerMap_ker) a)


end Natural

end
end Sporadic.Mathieu.M22ChapterH.Hexad.Action
