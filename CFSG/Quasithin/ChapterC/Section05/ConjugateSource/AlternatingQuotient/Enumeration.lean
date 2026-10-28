module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient.Action

/-!
# The four maximum elementary subgroups of the actual quotient

The descended marked action, central elementary D-image, and original
module coordinates supply every fixed-point profile. The actual conjugate
core is elementary, has full actor image, and has the same order as the
kernel. The generic B.2.21 lift theorem therefore gives exactly four
maximum elementary subgroups. This works for every kernel between Φ(D)
and D, including the source quotient and the paired-factor projection.

Source: Aschbacher–Smith C.5.6(5), printed pp.157–158.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
open RankOne
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G} {T : Type*} [Group T]

theorem quotient_fixedProfile (h : AlternatingPairSetup R K L) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (f : S R →* T) (hf : Function.Surjective f)
    (hPhi : (Phi R K).subgroupOf (S R) ≤ f.ker)
    (hk : f.ker ≤ (D R K).subgroupOf (S R)) :
    FixedProfile (quotientAction h f hf hk) (baumannImage R f (Q R K)) := by
  let : Finite T := Finite.of_surjective f hf
  rw [← quotientAction_kernel h f hf hk]
  refine marked_kernel_fixedProfile (quotientAction h f hf hk)
    (baumannImage R f (U K)) (baumannImage R f (D R K)) ?_ ?_ ?_
      (quotientCoordinates h f hk) (quotient_equivariant h f hf hk)
  · rw [quotientAction_kernel h f hf hk]
    have hp : Q R K = U K ⊔ D R K := h.product
    rw [hp]
    exact image_sup f (U K) (D R K) h.module_le inf_le_left
  · exact quotientAction_range h f hf hk
  · exact image_centralizer_central h x hx hnc f hf hPhi

/-- Enumeration on the literal image target, with the action constructed
from the source marking and with no family or fixed-profile premise. -/
theorem quotient_family_eq_four (h : AlternatingPairSetup R K L) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (f : S R →* T) (hf : Function.Surjective f)
    (hPhi : (Phi R K).subgroupOf (S R) ≤ f.ker)
    (hk : f.ker ≤ (D R K).subgroupOf (S R)) :
    ∃ B₀ B₁ : Subgroup T,
      Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T) =
        {baumannImage R f (Q R K),
          baumannImage R f ((Q R K).map (MulAut.conj x⁻¹).toMonoidHom), B₀, B₁} ∧
      B₀.map (quotientAction h f hf hk) = line 0 ∧
      B₁.map (quotientAction h f hf hk) = line 1 := by
  let : Finite T := Finite.of_surjective f hf
  have hVS : (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ S R :=
    (map_mono h.module_le).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx)))
  have himage : (baumannImage R f ((Q R K).map (MulAut.conj x⁻¹).toMonoidHom)).map
      (quotientAction h f hf hk) = ChapterB.Offenders.D 5 := by
    apply le_antisymm ((map_le_range _ _).trans (quotientAction_range h f hf hk).le)
    have hv := (image_action h f hf hk _ hVS).trans (h.conjugate_action_image x hx hnc)
    rw [← hv]
    apply map_mono
    apply map_mono
    exact subgroupOf_mono _ (map_mono (show U K ≤ Q R K from le_sup_left.trans_eq h.product.symm))
  exact exists_maxFamily_eq_four (quotientAction h f hf hk) _ _
    (h.quotient_core_elementary f hPhi) (opposite_elementary h x hx hnc f hPhi)
    (quotientAction_kernel h f hf hk) (quotientAction_range h f hf hk)
    himage (image_core_card h x hx hnc f hk) (quotient_fixedProfile h x hx hnc f hf hPhi hk)

/-- The source four-family on S/Φ(D), with its literal quotient map. -/
theorem frattini_quotient_family (h : AlternatingPairSetup R K L) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    letI := h.phi_normal
    let f := QuotientGroup.mk' ((Phi R K).subgroupOf (S R))
    ∃ B₀ B₁ : Subgroup ((S R) ⧸ (Phi R K).subgroupOf (S R)),
      Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup ((S R) ⧸ (Phi R K).subgroupOf (S R))) =
        {baumannImage R f (Q R K),
          baumannImage R f ((Q R K).map (MulAut.conj x⁻¹).toMonoidHom), B₀, B₁} ∧
      B₀.map (quotientAction h f (QuotientGroup.mk'_surjective _) (by
        rw [QuotientGroup.ker_mk']; exact subgroupOf_mono _ (map_subtype_le _))) = line 0 ∧
      B₁.map (quotientAction h f (QuotientGroup.mk'_surjective _) (by
        rw [QuotientGroup.ker_mk']; exact subgroupOf_mono _ (map_subtype_le _))) = line 1 := by
  let := h.phi_normal
  exact quotient_family_eq_four h x hx hnc (QuotientGroup.mk' ((Phi R K).subgroupOf (S R)))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (by rw [QuotientGroup.ker_mk']; exact subgroupOf_mono _ (map_subtype_le _))
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
end
