module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Cubic
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient

/-!
# The actual design projection of the native Mathieu extension

Conjugation on the perfect component, followed by its published central
quotient and the faithful design realization of Aut(M₂₂), gives a surjection
from the native binary matrix group to the full degree-22 design group.
Its kernel is precisely the cubic scalar subgroup. On the component the
map is the original marked degree-22 permutation action, and the component
maps onto the literal even subgroup of the design group.

The map is injective on any nonzero binary point centralizer, hence on the
source Borel. We name the full inverse images of hexad and partition
stabilizers and provide the actual restricted maps, their kernels, and
surjectivity. These interfaces retain the cubic layer for the remaining
local calculations; they do not assert their quotient structures.

Source: Aschbacher--Smith, 14.4.12, printed pp.1011--1012, and H.12.1(4--9),
printed pp.393--394. The carrier comparison and matrix attribution are those
of ActorCatalogue.Native. No identification from group order is used.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Sporadic.Mathieu
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics

noncomputable def componentProjection : M22TripleCover →* M22 :=
  M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (center M22TripleCover))

theorem componentProjection_apply_perm (g : M22TripleCover) :
    (componentProjection g : Equiv.Perm (Fin 22)) = corePermutationAction g := rfl

theorem componentProjection_ker : componentProjection.ker = center M22TripleCover := by
  rw [componentProjection, MonoidHom.ker_comp_of_injective _ _
    M22TripleCover.centralQuotientEquiv.injective, QuotientGroup.ker_mk']

theorem componentProjection_surjective : Function.Surjective componentProjection :=
  M22TripleCover.centralQuotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective (center M22TripleCover))

noncomputable def designProjection : Model →* m22DesignAut :=
  M22ValueBound.Concrete.designAutEquiv.symm.toMonoidHom.comp
    ((MulAut.congr M22TripleCover.centralQuotientEquiv).toMonoidHom.comp
      derivedQuotientConjugation)

theorem designProjection_surjective : Function.Surjective designProjection :=
  M22ValueBound.Concrete.designAutEquiv.symm.surjective.comp
    ((MulAut.congr M22TripleCover.centralQuotientEquiv).surjective.comp
      derivedQuotientConjugation_surjective)

theorem derivedConjugation_ker : derivedConjugation.ker = cubic := by
  rw [← centralizer_component_eq_cubic]
  ext g
  change (derivedGroup.normalizerMonoidHom (toDerivedNormalizer g) = 1) ↔ _
  change (toDerivedNormalizer g ∈ derivedGroup.normalizerMonoidHom.ker) ↔ _
  rw [normalizerMonoidHom_ker]
  change (g.val ∈ centralizer (derivedGroup : Set Matrix12ˣ)) ↔
    g ∈ centralizer (component : Set Model)
  constructor
  · intro h y hy
    exact Subtype.ext (h y.val hy)
  · intro h y hy
    exact congrArg (fun z : Model => z.val) (h (componentInclusion ⟨y, hy⟩) hy)

theorem designProjection_ker : designProjection.ker = cubic := by
  rw [designProjection,
    MonoidHom.ker_comp_of_injective _ _ M22ValueBound.Concrete.designAutEquiv.symm.injective,
    MonoidHom.ker_comp_of_injective _ _ (MulAut.congr M22TripleCover.centralQuotientEquiv).injective,
    derivedQuotientConjugation, MonoidHom.ker_comp_of_injective _ _
      MulAut.quotient_center_injective, derivedConjugation_ker]

noncomputable def cubicQuotientEquiv : (Model ⧸ cubic) ≃* m22DesignAut :=
  (QuotientGroup.quotientMulEquivOfEq designProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective designProjection designProjection_surjective)

theorem cubicQuotientEquiv_mk (g : Model) :
    cubicQuotientEquiv (QuotientGroup.mk' cubic g) = designProjection g := rfl

theorem designProjection_component (g : M22TripleCover) :
    designProjection (componentInclusion g) = M22ValueBound.Concrete.inclusion (componentProjection g) := by
  apply M22ValueBound.Concrete.designAutEquiv.injective
  change M22ValueBound.Concrete.designAutEquiv
    (M22ValueBound.Concrete.designAutEquiv.symm
      (MulAut.centralQuotientAction M22TripleCover.centralQuotientEquiv
        (derivedConjugation (componentInclusion g)))) = _
  rw [MulEquiv.apply_symm_apply, M22ValueBound.Concrete.designAutEquiv_inclusion]
  have hc : derivedConjugation (componentInclusion g) = MulAut.conj g := by
    ext x
    rfl
  rw [hc, MulAut.centralQuotientAction_conj]
  rfl

theorem component_map_designProjection : component.map designProjection = M22ValueBound.Concrete.inner := by
  rw [← M22ValueBound.Concrete.inclusion_range]
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨componentProjection ⟨x.val, hx⟩, (designProjection_component ⟨x.val, hx⟩).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := componentProjection_surjective x
    exact ⟨componentInclusion y, y.property, designProjection_component y⟩

theorem designProjection_injective_on_pointCentralizer {v : Space} (hv : v ≠ 0) :
    Function.Injective (designProjection.comp (pointCentralizer v).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [← MonoidHom.comap_ker, designProjection_ker]
  apply bot_unique
  intro x hx
  apply Subtype.ext
  exact (cubic_disjoint_pointCentralizer hv).le_bot ⟨hx, x.property⟩

theorem designProjection_injective_on_borel (B : Subgroup Model) {v : Space}
    (hv : v ≠ 0) (hB : B ≤ pointCentralizer v) :
    Function.Injective (designProjection.comp B.subtype) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : pointCentralizer v => z.val) (designProjection_injective_on_pointCentralizer hv
    (a₁ := ⟨x.val, hB x.property⟩) (a₂ := ⟨y.val, hB y.property⟩) h)

/-- The even design subgroup has exactly the original triple-cover component
as its full inverse image. -/
theorem component_preimage_designProjection :
    M22ValueBound.Concrete.inner.comap designProjection = component := by
  rw [← component_map_designProjection, comap_map_eq, designProjection_ker,
    sup_eq_left.mpr cubic_le_component]

/-- Restriction of the genuine design map to a full inverse image. -/
noncomputable def localProjection (P : Subgroup m22DesignAut) :
    P.comap designProjection →* P := designProjection.subgroupComap P

theorem localProjection_surjective (P : Subgroup m22DesignAut) :
    Function.Surjective (localProjection P) :=
  designProjection.subgroupComap_surjective_of_surjective P designProjection_surjective

theorem localProjection_ker (P : Subgroup m22DesignAut) :
    (localProjection P).ker = cubic.subgroupOf (P.comap designProjection) := by
  ext x
  change localProjection P x = 1 ↔ _
  rw [Subtype.ext_iff]
  change designProjection x.val = 1 ↔ _
  rw [← MonoidHom.mem_ker, designProjection_ker]
  rfl

theorem cubic_le_preimage (P : Subgroup m22DesignAut) : cubic ≤ P.comap designProjection := by
  rw [← designProjection_ker]
  exact ker_le_comap _ _

noncomputable def hexadPreimage (b : Finset (Fin 22)) : Subgroup Model :=
  (MulAction.stabilizer m22DesignAut b).comap designProjection

/-- The marked pair--hexad parabolic in the full design group. Its even
intersection is the published native pair--hexad subgroup of M₂₂. -/
noncomputable def outerPairHexad : Subgroup m22DesignAut :=
  MulAction.stabilizer m22DesignAut m22Hexad123 ⊓ M22ValueBound.Concrete.outerFirst

noncomputable def partitionPreimage : Subgroup Model :=
  M22ValueBound.Concrete.outerSecond.comap designProjection

theorem cubic_sup_eq_full_preimage (P : Subgroup Model) :
    cubic ⊔ P = (P.map designProjection).comap designProjection := by
  rw [comap_map_eq, designProjection_ker, sup_comm]

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
