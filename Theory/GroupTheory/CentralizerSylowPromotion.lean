module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# Promoting a centralizer Sylow subgroup

In a finite group, a Sylow two-subgroup of an involution centralizer is an
ambient Sylow subgroup if the center of its actual ambient image is generated
by that involution. The conclusion identifies the underlying subgroup exactly
with the image, so clients can transport chosen generators without conjugation.

Conjugation by the image's normalizer preserves its characteristic center and
therefore fixes the center's unique nonidentity element. Thus the normalizer
lies in the involution centralizer. The image's index in its normalizer divides
its index in the centralizer, which is odd by local Sylow maximality. The
normalizer-index congruence makes its ambient index odd as well.

This is the group-theoretic promotion used in Brauer's Desarguesian-plane
paper II, (4A), p. 129. The argument is independent of
the matrix-group hypotheses in that application.
-/

namespace Subgroup

private theorem normalizer_le_centralizer_of_center_image
    {G : Type*} [Group G] [Finite G] (subgroup : Subgroup G)
    (involution : G) (horder : orderOf involution = 2)
    (hcenter : (center subgroup).map subgroup.subtype = zpowers involution) :
    normalizer (subgroup : Set G) ≤ centralizer {involution} := by
  classical
  have hmem : involution ∈ (center subgroup).map subgroup.subtype := by
    rw [hcenter]
    exact mem_zpowers involution
  obtain ⟨centralElement, hcentral, hvalue⟩ := hmem
  change (centralElement : G) = involution at hvalue
  intro actor hactor
  let automorphism := subgroup.normalizerMonoidHom ⟨actor, hactor⟩
  have hcharacteristic := characteristic_iff_map_le.mp
    (inferInstance : (center subgroup).Characteristic) automorphism
  have hcentralImage := hcharacteristic (mem_map_of_mem automorphism.toMonoidHom hcentral)
  have hcyclic : (automorphism centralElement : G) ∈ zpowers involution := by
    rw [← hcenter]
    exact mem_map_of_mem subgroup.subtype hcentralImage
  have hne : (automorphism centralElement : G) ≠ 1 := by
    intro heq
    have hsub : automorphism centralElement = 1 := Subtype.ext heq
    have hone : centralElement = 1 := automorphism.injective (hsub.trans automorphism.map_one.symm)
    have : involution = 1 := hvalue.symm.trans (congrArg Subtype.val hone)
    simp [this] at horder
  rw [mem_zpowers_iff_mem_range_orderOf, horder] at hcyclic
  have hfixed : (automorphism centralElement : G) = involution := by
    obtain ⟨exponent, hexponent, heq⟩ := Finset.mem_image.mp hcyclic
    have hbound := Finset.mem_range.mp hexponent
    interval_cases exponent
    · exact False.elim (hne (by simpa using heq.symm))
    · simpa using heq.symm
  apply mem_centralizer_singleton_iff.mpr
  have hconjugate : actor * involution * actor⁻¹ = involution := by
    change actor * (centralElement : G) * actor⁻¹ = involution at hfixed
    rwa [hvalue] at hfixed
  exact mul_inv_eq_iff_eq_mul.mp hconjugate

private theorem exists_sylow_eq_of_normalizer_le
    {G : Type*} [Group G] [Finite G] {prime : ℕ} [Fact prime.Prime]
    (overgroup : Subgroup G) (localSylow : Sylow prime overgroup)
    (hnormalizer : normalizer ((localSylow : Subgroup overgroup).map
      overgroup.subtype : Set G) ≤ overgroup) :
    ∃ ambientSylow : Sylow prime G,
      (ambientSylow : Subgroup G) =
        (localSylow : Subgroup overgroup).map overgroup.subtype := by
  let image := (localSylow : Subgroup overgroup).map overgroup.subtype
  have hgroup : IsPGroup prime image := localSylow.isPGroup'.map _
  have hindex : image.relIndex overgroup = (localSylow : Subgroup overgroup).index := by
    simpa only [← MonoidHom.range_eq_map, overgroup.range_subtype, relIndex_top_right] using
      relIndex_map_map_of_injective (localSylow : Subgroup overgroup) ⊤
        overgroup.subtype_injective
  have hdiv : image.relIndex (normalizer image) ∣ image.relIndex overgroup := by
    exact dvd_of_mul_right_eq _ (relIndex_mul_relIndex image (normalizer image)
      overgroup le_normalizer hnormalizer)
  have hnot : ¬ prime ∣ image.relIndex (normalizer image) := by
    intro h
    exact localSylow.not_dvd_index (hindex ▸ h.trans hdiv)
  obtain ⟨height, hcard⟩ := hgroup.exists_card_eq
  have hcongr := Sylow.card_quotient_normalizer_modEq_card_quotient hcard
  have hambient : ¬ prime ∣ image.index := by
    intro h
    apply hnot
    exact (hcongr.dvd_iff dvd_rfl).mpr h
  exact ⟨hgroup.toSylow hambient, rfl⟩

public theorem exists_ambient_sylow_of_centralizer_center
    {G : Type*} [Group G] [Finite G]
    (involution : G) (horder : orderOf involution = 2)
    (localSylow : Sylow 2 (centralizer {involution}))
    (hcenter :
      let image := (localSylow : Subgroup (centralizer {involution})).map
        (centralizer {involution}).subtype
      (center image).map image.subtype = zpowers involution) :
    ∃ ambientSylow : Sylow 2 G,
      (ambientSylow : Subgroup G) =
        (localSylow : Subgroup (centralizer {involution})).map
          (centralizer {involution}).subtype := by
  exact exists_sylow_eq_of_normalizer_le _ localSylow
    (normalizer_le_centralizer_of_center_image _ involution horder hcenter)

end Subgroup
