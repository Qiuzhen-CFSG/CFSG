module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient.Images

/-!
# The actual alternating action after quotienting a centralizer kernel

Restrict the original marked action to S and descend it along the given
surjection. A kernel contained in D acts trivially and meets U trivially,
so the quotient action has the original sixteen-element core coordinates.
The equations record the actual quotient maps, rather than an abstract
isomorphic model of the action.

Source: Aschbacher–Smith C.5.6(5), printed pp.157–158.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
open RankOne
variable {G : Type*} [Group G] {R K L : Subgroup G} {T : Type*} [Group T]

noncomputable abbrev restriction (h : AlternatingPairSetup R K L) : S R →* FivePerm :=
  h.action.comp (inclusion (show S R ≤ K ⊔ S R from le_sup_right))

theorem restriction_kernel (h : AlternatingPairSetup R K L) :
    (restriction h).ker = (Q R K).subgroupOf (S R) := by
  ext s
  change inclusion le_sup_right s ∈ h.action.ker ↔ (s : G) ∈ Q R K
  rw [h.action_kernel]
  change (s : G) ∈ centralizer (U K : Set G) ↔ (s : G) ∈ Q R K
  have hc : Q R K = S R ⊓ centralizer (U K : Set G) := h.core
  rw [hc]
  exact (and_iff_right s.property).symm

theorem restriction_image (h : AlternatingPairSetup R K L) (B : Subgroup G) (hB : B ≤ S R) :
    (B.subgroupOf (S R)).map (restriction h) = (B.subgroupOf (K ⊔ S R)).map h.action := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨inclusion le_sup_right b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hB hb⟩, hb, rfl⟩

theorem restriction_range (h : AlternatingPairSetup R K L) :
    (restriction h).range = ChapterB.Offenders.D 5 := by
  have he := restriction_image h (S R) le_rfl
  rw [subgroupOf_self, ← MonoidHom.range_eq_map] at he
  exact he.trans h.baumann_image

/-- The descended action is constructed from the actual restricted source action. -/
noncomputable def quotientAction (h : AlternatingPairSetup R K L)
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker ≤ (D R K).subgroupOf (S R)) : T →* FivePerm :=
  f.liftOfSurjective hf ⟨restriction h, by
    rw [restriction_kernel]
    exact hk.trans (subgroupOf_mono _ (show D R K ≤ Q R K from le_sup_right.trans_eq h.product.symm))⟩

theorem quotientAction_comp (h : AlternatingPairSetup R K L)
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker ≤ (D R K).subgroupOf (S R)) :
    (quotientAction h f hf hk).comp f = restriction h := by
  simp [quotientAction]

theorem quotientAction_apply (h : AlternatingPairSetup R K L)
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker ≤ (D R K).subgroupOf (S R)) (s : S R) :
    quotientAction h f hf hk (f s) = restriction h s :=
  congrArg (fun a : S R →* FivePerm => a s) (quotientAction_comp h f hf hk)

theorem quotientAction_kernel (h : AlternatingPairSetup R K L)
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker ≤ (D R K).subgroupOf (S R)) :
    (quotientAction h f hf hk).ker = baumannImage R f (Q R K) := by
  ext t
  obtain ⟨s, rfl⟩ := hf t
  change quotientAction h f hf hk (f s) = 1 ↔ f s ∈ ((Q R K).subgroupOf (S R)).map f
  rw [quotientAction_apply, ← MonoidHom.mem_ker, restriction_kernel,
    ← mem_comap, comap_map_eq, sup_eq_left.mpr
      (hk.trans (subgroupOf_mono _ (show D R K ≤ Q R K from le_sup_right.trans_eq h.product.symm)))]

theorem quotientAction_range (h : AlternatingPairSetup R K L)
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker ≤ (D R K).subgroupOf (S R)) :
    (quotientAction h f hf hk).range = ChapterB.Offenders.D 5 := by
  have he := congrArg MonoidHom.range (quotientAction_comp h f hf hk)
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hf, ← MonoidHom.range_eq_map] at he
  exact he.trans (restriction_range h)

theorem image_action (h : AlternatingPairSetup R K L)
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker ≤ (D R K).subgroupOf (S R)) (B : Subgroup G) (hB : B ≤ S R) :
    (baumannImage R f B).map (quotientAction h f hf hk) =
      (B.subgroupOf (K ⊔ S R)).map h.action := by
  rw [baumannImage, map_map, quotientAction_comp, restriction_image h B hB]

/-- The original U-coordinates survive the actual quotient map. -/
noncomputable def quotientCoordinates (h : AlternatingPairSetup R K L)
    (f : S R →* T) (hk : f.ker ≤ (D R K).subgroupOf (S R)) :
    baumannImage R f (U K) ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
  (imageEquiv f hk (U K) h.module_le
    (alternatingModule_disjoint_of_commuting K (D R K) h.block inf_le_right)).symm.trans h.coordinates

theorem quotient_equivariant (h : AlternatingPairSetup R K L)
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker ≤ (D R K).subgroupOf (S R)) (t : T) (u : baumannImage R f (U K)) :
    ((quotientCoordinates h f hk).symm (Multiplicative.ofAdd
      (coreRepresentation (Fin 5) (quotientAction h f hf hk t)
        ((quotientCoordinates h f hk) u).toAdd)) : T) = t * (u : T) * t⁻¹ := by
  let e := imageEquiv f hk (U K) h.module_le
    (alternatingModule_disjoint_of_commuting K (D R K) h.block inf_le_right)
  obtain ⟨s, rfl⟩ := hf t
  obtain ⟨v, rfl⟩ := e.surjective u
  change (e (h.coordinates.symm (Multiplicative.ofAdd
    (coreRepresentation (Fin 5) (quotientAction h f hf hk (f s))
      (h.coordinates (e.symm (e v))).toAdd))) : T) = f s * (e v : T) * (f s)⁻¹
  rw [e.symm_apply_apply, quotientAction_apply]
  change f (inclusion h.module_le (h.coordinates.symm (Multiplicative.ofAdd
    (coreRepresentation (Fin 5) (restriction h s) (h.coordinates v).toAdd)))) =
      f s * f (inclusion h.module_le v) * (f s)⁻¹
  have he : inclusion h.module_le (h.coordinates.symm (Multiplicative.ofAdd
      (coreRepresentation (Fin 5) (restriction h s) (h.coordinates v).toAdd))) =
      s * inclusion h.module_le v * s⁻¹ :=
    Subtype.ext (h.equivariant (inclusion le_sup_right s) v)
  simpa only [map_mul, map_inv] using congrArg f he
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
end
