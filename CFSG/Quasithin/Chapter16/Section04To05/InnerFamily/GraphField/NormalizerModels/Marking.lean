module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.ModelData
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.Action
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.ResidualFixer

/-!
# Constructing the source graph-field marking

The actual equivalence L/O₂(L) ≃ PSL₃(4), together with the proved
center/two-core equality, defines a perfect central cover. The embedded
O²(C_L(r)) is identified with the fixed-subgroup residual. Its permitted
16.1.4(5) E₉ input then identifies its projective image with the concrete
matrix subgroup used by the pointwise-fixer calculation.

This construction applies to both the centerless group and its center-C₂
cover. It does not assume or construct a four-cover. The last fixer bound
still requires coverage of the full projective pointwise fixer by the
standard automorphism group; quaternion normalizers and fusion remain
separate calculations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(5) and 16.4.9(2), printed pp.1171, 1191–1192.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField.NormalizerModels
open Matrix.PSL3Four
open Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The actual central quotient map and marking of the source residual. -/
structure MarkedCover (L : Subgroup G) (r : G) where
  cover : PerfectCentralCovering.Cover L PSL
  kernel_center : cover.toMonoidHom.ker = center L
  kernel_two : IsPGroup 2 cover.toMonoidHom.ker
  actor_mem : r ∈ normalizer (L : Set G)
  compatible : ∀ x : L, cover.toMonoidHom (L.normalizerMonoidHom ⟨r, actor_mem⟩ x) =
    graphField (cover.toMonoidHom x)
  residual_image : ((residual L r).subgroupOf L).map cover.toMonoidHom = model

omit [Finite G] in
/-- Restricting the embedded residual to L gives its genuine fixed-subgroup residual. -/
theorem residual_subgroupOf_eq (hn : r ∈ normalizer (L : Set G)) :
    (residual L r).subgroupOf L =
      (pResidual 2 (L.normalizerMonoidHom ⟨r, hn⟩).fixedSubgroup).map
        (L.normalizerMonoidHom ⟨r, hn⟩).fixedSubgroup.subtype := by
  apply Subgroup.map_injective L.subtype_injective
  rw [map_subgroupOf_eq_of_le ((residual_le_centralizer L r).trans inf_le_left)]
  let e := ComponentTransfer.Intrinsic.centralizerEquivFixed hn
  change residual L r =
    ((pResidual 2 (ComponentTransfer.Intrinsic.action hn).fixedSubgroup).map
      (ComponentTransfer.Intrinsic.action hn).fixedSubgroup.subtype).map L.subtype
  rw [← map_pResidual 2 e, map_map, map_map]
  rfl

/-- Source 16.1.4(5), supplied as an actual E₉ residual, constructs the marked
perfect central cover and identifies its image with the concrete diagonal/cycle E₉. -/
noncomputable def markedCover {𝒦 : GroupClass}
    (hG : Hypothesis1611 𝒦 G) (h : IntersectionSetup T z L g R)
    (hmodel : IsL3FourGraphField L r)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9) :
    MarkedCover L r := by
  apply Classical.choice
  let := h.component.quasisimple
  obtain ⟨hn, e, he⟩ := hmodel
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : f.ker = pCore 2 L := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hZ : center L = pCore 2 L :=
    hG.evenType.component_center_eq_twoCore h.involution h.component
  let c : PerfectCentralCovering.Cover L PSL := {
    toMonoidHom := f
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))
    isPerfect := inferInstance
    ker_le_center := by rw [hf, hZ] }
  have hp : IsPGroup 2 c.toMonoidHom.ker := by
    change IsPGroup 2 f.ker
    rw [hf]
    exact pCore_isPGroup
  have he' (x : L) : c.toMonoidHom (L.normalizerMonoidHom ⟨r, hn⟩ x) =
      graphField (c.toMonoidHom x) := he x
  refine ⟨⟨c, hf.trans hZ.symm, hp, hn, he', ?_⟩⟩
  have hle := (residual_le_centralizer L r).trans inf_le_left
  let a := L.normalizerMonoidHom ⟨r, hn⟩
  have hrD := residual_subgroupOf_eq hn
  let := hD
  have h3 : IsPGroup 3 ((residual L r).subgroupOf L) :=
    (IsElementaryAbelian.isPGroup 3 (residual L r)).of_equiv
      (subgroupOfEquivOfLe hle).symm
  have hc : Nat.card ((residual L r).subgroupOf L) = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans h9
  rw [hrD] at h3 hc ⊢
  exact InnerFamilyNormalizer.residual_image_eq_model c hp a he' h3 hc

omit [Finite G] in
/-- The descended marked actor is exactly inverse transpose times Frobenius. -/
theorem MarkedCover.actor_descends (d : MarkedCover L r) :
    d.cover.autMap d.kernel_center (L.normalizerMonoidHom ⟨r, d.actor_mem⟩) =
      graphField := by
  ext x
  obtain ⟨y, rfl⟩ := d.cover.surjective x
  rw [d.cover.autMap_apply, d.compatible]

omit [Finite G] in
/-- Transfer of the standard model fixer through the constructed source marking.
Coverage of the full projective pointwise fixer is a separate, explicit obligation. -/
theorem MarkedCover.residual_fixer_of_standard (d : MarkedCover L r)
    (hstandard : fixingSubgroup (MulAut PSL) (model : Set PSL) ≤
      Matrix.PSL3.OuterSolvable.standard F) :
    normalizer (L : Set G) ⊓ centralizer (residual L r : Set G) ≤
      (centralizer (L : Set G) ⊔ residual L r) ⊔ zpowers r :=
  InnerFamilyNormalizer.residual_fixer_bound L (residual L r) d.cover d.kernel_center
    d.residual_image ⟨r, d.actor_mem⟩ d.actor_descends hstandard

/-- Every element of LE fixes the marked z, including the requested Q. -/
theorem product_le_centralizer_z (h : IntersectionSetup T z L g R) (hr : r ∈ R) :
    L ⊔ fourGroup r z ≤ centralizer ({z} : Set G) := by
  apply sup_le h.component.1
  apply sup_le
  · exact zpowers_le.mpr (h.sylow_centralizes (h.le_sylow hr))
  · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)

/-- The source cover has center of order two, not a Klein four-group. -/
theorem center_card_two (h : IntersectionSetup T z L g R)
    (hTC : commutingSylow T L = zpowers z)
    (hcenter : center L = pCore 2 L) (hcore : pCore 2 L ≠ ⊥) :
    Nat.card (center L) = 2 := by
  have hc := center_eq_zpowers_of_nontrivial_core h hTC hcenter hcore
  have hm := congrArg (fun D : Subgroup G => Nat.card D) hc
  simpa only [card_map_of_injective L.subtype_injective, Nat.card_zpowers, h.involution]
    using hm

end CFSG.Quasithin.Chapter16.Intersections.GraphField.NormalizerModels
