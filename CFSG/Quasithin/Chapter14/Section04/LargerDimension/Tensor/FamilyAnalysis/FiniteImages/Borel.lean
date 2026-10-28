module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.FiniteImages.Residual
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.Representation.BinaryAlternatingFiveBorel

/-!
# The actual Borel in the tensor quotient

Intersect the supplied Sylow subgroup with the relatively normal H∞. The
surjection from H∞ onto its actual star image maps this Sylow normalizer onto
the image Sylow normalizer. The marked A₅ calculation then identifies it with
an A₄ point stabilizer. Kernel containment also preserves the intersection
with T, giving the literal relative-normalizer formula in H/O₂(H).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.4.10(1), printed p.1010, under case 14.4.2(5), printed p.1006.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem component_le (H : Subgroup G) : component H ≤ H := map_subtype_le _
omit [Finite G] in
private theorem star_mono (H : Subgroup G) {X Y : Subgroup G} (h : X ≤ Y) :
    star H X ≤ star H Y := map_mono (subgroupOf_mono H h)
omit [Finite G] in
private theorem starHom_surjective {H K : Subgroup G} (hK : K ≤ H) :
    Function.Surjective (starHom hK) :=
  ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hK).symm.surjective

omit [Finite G] in
private theorem star_subgroupOf_map {H K X : Subgroup G} (hK : K ≤ H) (hX : X ≤ K) :
    (X.subgroupOf K).map (starHom hK) = (star H X).subgroupOf (star H K) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hK x.property⟩, hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨⟨x, hX hx⟩, hx, ?_⟩
    exact Subtype.ext hxy

private theorem exists_component_sylow {H T : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T) :
    ∃ R : Sylow 2 (component H),
      (R : Subgroup (component H)).map (component H).subtype = T ⊓ component H := by
  have hn : H ≤ normalizer (component H : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (solvableResidual H))
  simpa only [hP] using P.exists_map_subtype_eq_inf_of_normalizes (component_le H) hn

omit [Finite G] in
private theorem borel_subgroupOf {H T : Subgroup G} (R : Sylow 2 (component H))
    (hR : (R : Subgroup (component H)).map (component H).subtype = T ⊓ component H) :
    (borel H T).subgroupOf (component H) = normalizer (R : Set (component H)) := by
  have he : (T ⊓ component H).subgroupOf (component H) = (R : Subgroup (component H)) := by
    rw [← hR]
    exact comap_map_eq_self_of_injective (component H).subtype_injective _
  change ((component H) ⊓ normalizer ((T ⊓ component H : Subgroup G) : Set G)).subgroupOf _ = _
  rw [inf_subgroupOf_left, subgroupOf_normalizer_eq inf_le_right, he]
  rfl

/-- The actual Borel image is the normalizer of a Sylow subgroup of the actual component image. -/
theorem exists_star_borel_normalizer {H T : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T) :
    ∃ Q : Sylow 2 (star H (component H)),
      (star H (borel H T)).subgroupOf (star H (component H)) = normalizer (Q : Set _) := by
  obtain ⟨R, hR⟩ := exists_component_sylow P hP
  let f := starHom (component_le H)
  refine ⟨R.mapSurjective (starHom_surjective (component_le H)), ?_⟩
  rw [← star_subgroupOf_map (component_le H) (show borel H T ≤ component H from inf_le_left),
    borel_subgroupOf R hR]
  exact R.normalizer_map_surjective f (starHom_surjective (component_le H))

omit [Finite G] in
private theorem star_inter_of_core_le {H T K : Subgroup G} (hcore : twoCore H ≤ T) :
    star H (T ⊓ K) = star H T ⊓ star H K := by
  have hk : (QuotientGroup.mk' (pCore 2 H)).ker ≤ T.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact hcore (mem_map.mpr ⟨x, hx, rfl⟩)
  unfold star
  change ((T.subgroupOf H ⊓ K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = _
  rw [inf_comm (T.subgroupOf H), map_inf_of_ker_le _ _ _ hk, inf_comm]

/-- Transport the literal relative normalizer, with the same intersection with T. -/
theorem star_borel_eq_relative_normalizer {H T : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T) :
    star H (borel H T) = star H (component H) ⊓
      normalizer ((star H T ⊓ star H (component H) : Subgroup (coreQuotient H)) : Set _) := by
  let K := component H
  let f := starHom (component_le H)
  obtain ⟨R, hR⟩ := exists_component_sylow P hP
  have hRi : (R : Subgroup K) = (T ⊓ K).subgroupOf K := by
    rw [← hR]
    exact (comap_map_eq_self_of_injective K.subtype_injective _).symm
  have hRm : (R : Subgroup K).map f =
      (star H T ⊓ star H K).subgroupOf (star H K) := by
    rw [hRi, star_subgroupOf_map (component_le H) inf_le_right,
      star_inter_of_core_le (twoCore_le_of_sylow P hP)]
  have hB : (star H (borel H T)).subgroupOf (star H K) =
      (star H K ⊓ normalizer ((star H T ⊓ star H K : Subgroup (coreQuotient H)) : Set _)).subgroupOf
        (star H K) := by
    rw [← star_subgroupOf_map (component_le H) (show borel H T ≤ K from inf_le_left),
      borel_subgroupOf R hR]
    rw [R.normalizer_map_surjective f (starHom_surjective (component_le H)), hRm,
      inf_subgroupOf_left, subgroupOf_normalizer_eq inf_le_right]
  have hm := congrArg (Subgroup.map (star H K).subtype) hB
  simpa only [map_subgroupOf_eq_of_le (star_mono H (show borel H T ≤ K from inf_le_left)),
    map_subgroupOf_eq_of_le inf_le_left] using hm

/-- Point-stabilizer placement under any prescribed A₅ marking of the component image. -/
theorem exists_star_borel_stabilizer {H T : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T)
    (eK : star H (component H) ≃* AltFive) :
    ∃ i : Fin 5, ((star H (borel H T)).subgroupOf (star H (component H))).map eK.toMonoidHom =
      MulAction.stabilizer AltFive i := by
  obtain ⟨Q, hQ⟩ := exists_star_borel_normalizer P hP
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer
    (Q.mapSurjective (f := eK.toMonoidHom) eK.surjective)
  refine ⟨i, ?_⟩
  rw [hQ]
  change (normalizer ((Q : Subgroup (star H (component H))) : Set _)).map eK.toMonoidHom = _
  rw [map_equiv_normalizer_eq]
  exact hi

/-- The actual Borel image is A₄, without assuming a Borel-image certificate. -/
theorem exists_star_borel_equiv {H T : Subgroup G} (P : Sylow 2 H)
    (hP : (P : Subgroup H).map H.subtype = T)
    (hmodel : Nonempty (coreQuotient H ≃* Three × Five) ∨
      Nonempty (coreQuotient H ≃* Three × AltFive)) :
    Nonempty (star H (borel H T) ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨eK⟩ := exists_starComponentEquiv hmodel
  obtain ⟨i, hi⟩ := exists_star_borel_stabilizer P hP eK
  have ht : ∀ j : Fin 5, ∃ g : AltFive, g.val j = 4 := by decide +kernel
  obtain ⟨g, hg⟩ := ht i
  let e₁ := (subgroupOfEquivOfLe (star_mono H (show borel H T ≤ component H from inf_le_left))).symm
  let e₂ := (eK.subgroupMap _).trans (MulEquiv.subgroupCongr hi)
  let e₃ : MulAction.stabilizer AltFive i ≃* MulAction.stabilizer AltFive (4 : Fin 5) :=
    MulAction.stabilizerEquivStabilizer (show (4 : Fin 5) = g • i from hg.symm)
  exact ⟨e₁.trans (e₂.trans (e₃.trans BinaryPermutation.AlternatingFiveBorel.marking.symm))⟩
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
