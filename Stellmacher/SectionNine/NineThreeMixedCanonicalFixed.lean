module
public import Stellmacher.SectionNine.NineThreeMixedGeometry
public import Stellmacher.SectionNine.NineThreeNormalizedPairCentralizer
public import Stellmacher.SectionNine.NineThreeCanonicalFixedGeneration

/-!
# No canonical fixed vectors in the actual mixed commutator

The normalized extracted pair centralizes the mixed subgroup. Apply the
canonical fixed-vector consequence of (6.4) to the second extracted group:
a canonical fixed vector in the mixed subgroup lies in the next center.
That center centralizes the native Baumann subgroup, whereas the proved
mixed/Baumann intersection is trivial.

This argument uses the full canonical preimage, not an unsupported equality
between native and barred Thompson subgroups. Source: Stellmacher (9.3),
printed p.50, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_mixed_canonical_fixed_bot
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hcritical : sectionSixBarredCritical ctx.hypothesisTwo ≠ ⊥) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    mixed ⊓ (Subgroup.centralizer
      (sectionSixBarredCriticalPreimage ctx.hypothesisTwo : Set H)).comap embedding = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let vertex := Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt Γ cp.a ⊓ GAt Γ vertex, ZAt Γ vertex ⊓ GAt Γ cp.a⁆ : Subgroup G)
  let extracted := second.E.map (MulAut.conj config.g⁻¹).toMonoidHom
  have hpair := nine_three_normalized_pair_centralizer ctx hb hlarge first second config
  have hgenerate : extracted ⊔ (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) =
      GAt Γ cp.firstStep := by
    rw [inf_comm, ← config.second_new_vertex]
    exact config.second_geometry.edge_generated
  have hcentral : mixed ≤ Subgroup.centralizer (extracted : Set G) := by
    intro vector hvector
    rw [Subgroup.mem_centralizer_iff]
    intro actor hactor
    apply ctx.embedding_injective
    have hactorImage := hpair.2 (Subgroup.mem_sup_right
      (Subgroup.mem_map_of_mem embedding hactor))
    simpa only [map_mul] using (Subgroup.mem_centralizer_iff.mp hactorImage
      (embedding vector) (Subgroup.mem_map_of_mem embedding hvector)).symm
  have hnext : ZAt Γ cp.firstStep ≤ Subgroup.centralizer (baumannIn T : Set G) := by
    rw [show ZAt Γ cp.firstStep = omegaOneCenter T from
      (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center.1]
    exact (omegaOneCenter_le_centerAmbient T).trans ((centerAmbient_le_centralizer T).trans
      (Subgroup.centralizer_le (show baumannIn T ≤ T from inf_le_left)))
  have hzero := nine_three_normalized_baumann_fixed_commutator_bot
    ctx hb hlarge first second config
  apply bot_unique
  intro vector hvector
  have hfixed : vector ∈ ZAt Γ cp.firstStep :=
    nine_three_canonical_fixed_generation ctx hcritical extracted hgenerate vector
      (hpair.1 hvector.1) hvector.2 (hcentral hvector.1)
  exact hzero.le ⟨hvector.1, hnext hfixed⟩

end Stellmacher.SectionNine
