module

public import Theory.GroupAction.ExtendingSubgroupAutomorphisms

/-!
# Transport of full and inner pair restriction images

An ambient group equivalence taking both subgroups to another pair carries
all extending automorphisms to the new pair. Conjugation actors correspond
by that same equivalence, so the entire inner restriction image also
transports exactly. The subgroup equivalence is required to agree with the
ambient map, retaining the actual action in any subsequent plane coordinates.

These general transport lemmas connect the literal Held representatives to
arbitrary locally placed pairs. They assume no automorphism realization or
local-overgroup stabilization by the extending actors.
Source context: Aschbacher–Smith, printed pp.509–511; GLS3 Table 5.3p.
-/

public section
open Subgroup
namespace Held.LocalPairs.PairCoverage.LocalActions.Transport
variable {G H : Type*} [Group G] [Group H]

private theorem preserves_congr (e : G ≃* H) {S : Subgroup G} {T : Subgroup H}
    (hS : ∀ x, e x ∈ T ↔ x ∈ S) (b : MulAut G)
    (hb : ∀ x, b x ∈ S ↔ x ∈ S) :
    ∀ x, MulAut.congr e b x ∈ T ↔ x ∈ T := by
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  change e (b (e.symm (e y))) ∈ T ↔ e y ∈ T
  rw [e.symm_apply_apply, hS, hS]
  exact hb y

private theorem inverse_compatible (e : G ≃* H) {R : Subgroup G} {U : Subgroup H}
    (f : R ≃* U) (hf : ∀ x : R, (f x : H) = e x) (x : U) :
    (f.symm x : G) = e.symm x := by
  apply e.injective
  rw [e.apply_symm_apply, ← hf, f.apply_symm_apply]

private theorem inverse_membership (e : G ≃* H) {S : Subgroup G} {T : Subgroup H}
    (hS : ∀ x, e x ∈ T ↔ x ∈ S) (x : H) :
    e.symm x ∈ S ↔ x ∈ T := by
  simpa only [e.apply_symm_apply] using (hS (e.symm x)).symm

private theorem congr_symm_cancel {R U : Type*} [Group R] [Group U]
    (f : R ≃* U) (a : MulAut U) :
    MulAut.congr f (MulAut.congr f.symm a) = a := by
  ext x
  change f (f.symm (a (f (f.symm x)))) = a x
  rw [f.apply_symm_apply, f.apply_symm_apply]

private theorem restriction_mem_transport (e : G ≃* H)
    {S R : Subgroup G} {T U : Subgroup H}
    (hS : ∀ x, e x ∈ T ↔ x ∈ S)
    (f : R ≃* U) (hf : ∀ x : R, (f x : H) = e x)
    {a : MulAut R} (ha : a ∈ (pairRestriction S R).range) :
    MulAut.congr f a ∈ (pairRestriction T U).range := by
  obtain ⟨b, hb, hab⟩ := (mem_pairRestriction_range_iff S R a).mp ha
  apply (mem_pairRestriction_range_iff T U _).mpr
  refine ⟨MulAut.congr e b, preserves_congr e hS b hb, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := f.surjective x
  change (f (a (f.symm (f y))) : H) = e (b (e.symm (f y : H)))
  rw [f.symm_apply_apply, hf, hf, e.symm_apply_apply, hab]

/-- An ambient equivalence transports the complete extending restriction image. -/
theorem pairRestriction_range_map (e : G ≃* H)
    {S R : Subgroup G} {T U : Subgroup H}
    (hS : ∀ x, e x ∈ T ↔ x ∈ S)
    (f : R ≃* U) (hf : ∀ x : R, (f x : H) = e x) :
    ((pairRestriction S R).range).map (MulAut.congr f).toMonoidHom =
      (pairRestriction T U).range := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact restriction_mem_transport e hS f hf ha
  · intro a ha
    exact ⟨MulAut.congr f.symm a,
      restriction_mem_transport e.symm (inverse_membership e hS)
        f.symm (inverse_compatible e f hf) ha, congr_symm_cancel f a⟩

private theorem inner_mem_transport (e : G ≃* H)
    {S R : Subgroup G} {T U : Subgroup H}
    (hS : ∀ x, e x ∈ T ↔ x ∈ S) (hR : ∀ x, e x ∈ U ↔ x ∈ R)
    (f : R ≃* U) (hf : ∀ x : R, (f x : H) = e x)
    {a : MulAut R} (ha : a ∈ (actingPairRestriction (MulAut.conj : G →* MulAut G) S R).range) :
    MulAut.congr f a ∈ (actingPairRestriction (MulAut.conj : H →* MulAut H) T U).range := by
  obtain ⟨g, rfl⟩ := ha
  have hc : MulAut.conj (e g.val) = MulAut.congr e (MulAut.conj g.val) := by
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hg : MulAut.conj (e g.val) ∈ automorphismPairStabilizer T U := by
    rw [hc, mem_automorphismPairStabilizer_iff]
    have h := (mem_automorphismPairStabilizer_iff S R _).mp g.property
    exact ⟨preserves_congr e hS _ h.1, preserves_congr e hR _ h.2⟩
  refine ⟨⟨e g.val, hg⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := f.surjective x
  apply Subtype.ext
  change e g.val * (f y : H) * (e g.val)⁻¹ =
    (f (actingPairRestriction (MulAut.conj : G →* MulAut G) S R g
      (f.symm (f y))) : H)
  rw [f.symm_apply_apply, hf, hf, actingPairRestriction_apply]
  simp only [MulAut.conj_apply, map_mul, map_inv]

/-- The same ambient equivalence transports the inner restriction image exactly. -/
theorem innerRestriction_range_map (e : G ≃* H)
    {S R : Subgroup G} {T U : Subgroup H}
    (hS : ∀ x, e x ∈ T ↔ x ∈ S) (hR : ∀ x, e x ∈ U ↔ x ∈ R)
    (f : R ≃* U) (hf : ∀ x : R, (f x : H) = e x) :
    ((actingPairRestriction (MulAut.conj : G →* MulAut G) S R).range).map
        (MulAut.congr f).toMonoidHom =
      (actingPairRestriction (MulAut.conj : H →* MulAut H) T U).range := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact inner_mem_transport e hS hR f hf ha
  · intro a ha
    exact ⟨MulAut.congr f.symm a,
      inner_mem_transport e.symm (inverse_membership e hS) (inverse_membership e hR)
        f.symm (inverse_compatible e f hf) ha, congr_symm_cancel f a⟩

/-- Compose coordinate changes before mapping an action subgroup. -/
theorem map_congr_trans {R U V : Type*} [Group R] [Group U] [Group V]
    (A : Subgroup (MulAut R)) (f : R ≃* U) (e : U ≃* V) :
    A.map (MulAut.congr (f.trans e)).toMonoidHom =
      (A.map (MulAut.congr f).toMonoidHom).map (MulAut.congr e).toMonoidHom := by
  rw [map_map]
  rfl

/-- A subgroup image equality supplies the membership equivalence used above. -/
theorem membership_of_map_eq (e : G ≃* H) {S : Subgroup G} {T : Subgroup H}
    (hS : S.map e.toMonoidHom = T) (x : G) : e x ∈ T ↔ x ∈ S := by
  rw [← hS, mem_map_equiv, e.symm_apply_apply]

end Held.LocalPairs.PairCoverage.LocalActions.Transport
