module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.SourceCases

/-!
# The component central quotient in the single-component branch

E.2.2 recognizes the component in H/J, whereas the local module is acted
on by H/O₂(H). Restricting the canonical quotient map to the component
image gives a surjection. The single-case kernel clause identifies its
kernel with the component center, so the first isomorphism theorem supplies
a canonical central-quotient equivalence. This same map carries the actual
M∩K overlap to the source overlap.

This does not split the cover, kill its center, or identify SU₃ with PSU₃.
Those model-dependent steps remain separate from this comparison.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.2.2(2),
printed pp.215--216, and the single-component deduction on p.1152.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
open BorelReduction
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
variable {G : Type*} [Group G] {H M K T : Subgroup G}

/-- The restriction of H/O₂(H) → H/J to the literal component image. -/
def componentToSource (hcore : pCore 2 H ≤ sourceKernel H M) :
    actorImage H K →* sourceImage H M K :=
  ((actorToSource hcore).comp (actorImage H K).subtype).codRestrict _ (by
    intro k
    rw [← actorToSource_image hcore]
    exact mem_map_of_mem _ k.property)

theorem componentToSource_surjective (hcore : pCore 2 H ≤ sourceKernel H M) :
    Function.Surjective (componentToSource (K := K) hcore) := by
  rintro ⟨x, hx⟩
  rw [← actorToSource_image hcore] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨⟨k, hk⟩, rfl⟩

theorem componentToSource_ker (hcore : pCore 2 H ≤ sourceKernel H M)
    (hc : SourceCases.SingleClauses H M K T) :
    (componentToSource (K := K) hcore).ker = center (actorImage H K) := by
  have hk : (actorToSource hcore).ker =
      (center (actorImage H K)).map (actorImage H K).subtype := by
    have hm := QuotientGroup.ker_map (pCore 2 H) (sourceKernel H M) (MonoidHom.id H) hcore
    exact hm.trans (by simpa using hc.kernel_center)
  ext k
  change componentToSource hcore k = 1 ↔ _
  rw [Subtype.ext_iff]
  change (k : H ⧸ pCore 2 H) ∈ (actorToSource hcore).ker ↔ _
  rw [hk]
  constructor
  · rintro ⟨z, hz, he⟩
    exact (Subtype.ext he : z = k) ▸ hz
  · intro h
    exact ⟨k, h, rfl⟩

/-- The component modulo its entire center is the E.2.2 source component. -/
noncomputable def componentCentralQuotientEquiv
    (hcore : pCore 2 H ≤ sourceKernel H M) (hc : SourceCases.SingleClauses H M K T) :
    actorImage H K ⧸ center (actorImage H K) ≃* sourceImage H M K :=
  (QuotientGroup.quotientMulEquivOfEq (componentToSource_ker hcore hc).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (componentToSource_surjective hcore))

theorem componentCentralQuotientEquiv_mk
    (hcore : pCore 2 H ≤ sourceKernel H M) (hc : SourceCases.SingleClauses H M K T)
    (k : actorImage H K) :
    componentCentralQuotientEquiv hcore hc (QuotientGroup.mk' _ k) =
      componentToSource hcore k := rfl

/-- The actual overlap survives under the same map used for the component. -/
theorem componentToSource_overlap (hcore : pCore 2 H ≤ sourceKernel H M) :
    ((actorImage H (M ⊓ K)).subgroupOf (actorImage H K)).map (componentToSource hcore) =
      SourceCases.componentOverlap H M K := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    change actorToSource hcore k ∈ sourceImage H M (M ⊓ K)
    rw [← actorToSource_image hcore]
    exact mem_map_of_mem _ hk
  · intro hx
    change (x : H ⧸ sourceKernel H M) ∈ sourceImage H M (M ⊓ K) at hx
    rw [← actorToSource_image hcore] at hx
    obtain ⟨k, hk, he⟩ := hx
    have hkK : k ∈ actorImage H K := (map_mono (comap_mono inf_le_right)) hk
    exact ⟨⟨k, hkK⟩, hk, Subtype.ext he⟩

theorem componentCentralQuotientEquiv_overlap
    (hcore : pCore 2 H ≤ sourceKernel H M) (hc : SourceCases.SingleClauses H M K T) :
    (((actorImage H (M ⊓ K)).subgroupOf (actorImage H K)).map
      (QuotientGroup.mk' (center (actorImage H K)))).map
      (componentCentralQuotientEquiv hcore hc).toMonoidHom =
      SourceCases.componentOverlap H M K := by
  rw [map_map]
  exact componentToSource_overlap hcore

/-- K=K₀ rules out the genuinely exchanged E.2.2 alternative. -/
theorem single_source_cases [Finite G] {f : ℕ}
    (h : SourceCases.ReducedCases H M K T f)
    (hsingle : conjugateSpanBy K T = K) :
    SourceCases.SingleClauses H M K T ∧
      (SourceCases.BenderModel H M K f ∨ SourceCases.DiagramModel H M K T f) := by
  cases h with
  | exchanged hc _ =>
    obtain ⟨t, ht, hne, _⟩ := hc.exchanged_product
    have hn : T ≤ normalizer (K : Set G) :=
      hsingle ▸ le_normalizer_conjugateSpanBy K T
    exact (hne (mem_normalizer_iff_map_conj_eq.mp (hn (T.inv_mem ht))).symm).elim
  | bender hc hm => exact ⟨hc, Or.inl hm⟩
  | diagram hc hm => exact ⟨hc, Or.inr hm⟩

/-- The source Borel recognition also recognizes the central quotient of
the representation component, using the canonical comparison map. -/
theorem central_quotient_borel_pair {E : Type*} [Group E] (B : Subgroup E)
    (hcore : pCore 2 H ≤ sourceKernel H M)
    (hc : SourceCases.SingleClauses H M K T)
    (hm : SourceCases.ModelBorelPair H M K B) :
    ∃ e : actorImage H K ⧸ center (actorImage H K) ≃* E,
      (((actorImage H (M ⊓ K)).subgroupOf (actorImage H K)).map
        (QuotientGroup.mk' (center (actorImage H K)))).map e.toMonoidHom = B := by
  obtain ⟨e, he⟩ := hm
  refine ⟨(componentCentralQuotientEquiv hcore hc).trans e, ?_⟩
  change Subgroup.map (e.toMonoidHom.comp (componentCentralQuotientEquiv hcore hc).toMonoidHom) _ = B
  rw [← map_map, componentCentralQuotientEquiv_overlap, he]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
