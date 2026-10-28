module

public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts

/-!
# The initial-orbit neighbor-center join

In the commuting critical-pair setting, (7.5) identifies the first-step
center with the omega-one center of the distinguished Sylow subgroup.
Local transitivity and Sylow conjugacy then identify the neighbor-center
join with the initial vertex's Sylow-center join. Every neighbor center
is nontrivial and lies in that join. Covariance transports these conclusions
to the entire initial orbit, without rank or quotient-model assumptions.

The ambient interface keeps Hypothesis Two on the original group and
retains the embedding of the graph group. The proof uses only the local
Section Seven hypotheses and the commuting critical pair.

Source: Stellmacher (7.5), printed pp.34–35, and the neighbor-center lines
in (9.7), printed p.53, `refs/files/stellmacher-n-group.pdf`.
-/

open scoped Pointwise

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem centerJoin_omega_map
    {G G' : Type u} [Group G] [Group G']
    (equiv : G ≃* G') (subgroup : Subgroup G) :
    omegaOneCenter (subgroup.map equiv.toMonoidHom) =
      (omegaOneCenter subgroup).map equiv.toMonoidHom := by
  let subgroupEquiv := subgroup.equivMapOfInjective equiv.toMonoidHom equiv.injective
  let centerEquiv := Subgroup.centerCongr subgroupEquiv
  have omegaMap :
      (omega₁ (G := Subgroup.center subgroup) (p := 2)).map centerEquiv.toMonoidHom =
        omega₁ (G := Subgroup.center (subgroup.map equiv.toMonoidHom)) (p := 2) := by
    change (Subgroup.closure {element | element ^ (2 ^ 1) = 1}).map
      centerEquiv.toMonoidHom = Subgroup.closure {element | element ^ (2 ^ 1) = 1}
    rw [MonoidHom.map_closure]
    congr 1
    ext element
    constructor
    · rintro ⟨preimage, hpreimage, rfl⟩
      change centerEquiv preimage ^ (2 ^ 1) = 1
      rw [← map_pow, hpreimage, map_one]
    · intro helement
      refine ⟨centerEquiv.symm element, ?_, centerEquiv.apply_symm_apply element⟩
      change centerEquiv.symm element ^ (2 ^ 1) = 1
      rw [← map_pow, helement, map_one]
  symm
  unfold omegaOneCenter
  rw [← omegaMap]
  simp only [Subgroup.map_map]
  apply congrArg (fun hom : Subgroup.center subgroup →* G' ↦
    (omega₁ (G := Subgroup.center subgroup) (p := 2)).map hom)
  ext element
  rfl

private theorem centerJoin_sylow_smul
    {G : Type u} [Group G] (subgroup : Subgroup G)
    (sylow : Sylow 2 subgroup) (element : subgroup) :
    (((element • sylow : Sylow 2 subgroup) : Subgroup subgroup).map subgroup.subtype) =
      (((sylow : Subgroup subgroup).map subgroup.subtype).map
        (MulAut.conj (element : G)).toMonoidHom) := by
  change (((sylow : Subgroup subgroup).map
    (MulAut.conj element).toMonoidHom).map subgroup.subtype) = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem centerJoin_omega_nontrivial
    {G : Type u} [Group G] [Finite G]
    (subgroup : Subgroup G) (hp : IsPGroup 2 subgroup) (hne : subgroup ≠ ⊥) :
    omegaOneCenter subgroup ≠ ⊥ := by
  let _ : Nontrivial subgroup := (Subgroup.nontrivial_iff_ne_bot subgroup).2 hne
  let _ : Nontrivial (Subgroup.center subgroup) := hp.center_nontrivial
  have hcenter := hp.to_subgroup (Subgroup.center subgroup)
  obtain ⟨exponent, hpositive, hcard⟩ := hcenter.nontrivial_iff_card.mp inferInstance
  have hdiv : 2 ∣ Nat.card (Subgroup.center subgroup) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hpositive)
  have hinner := omega₁_map_subtype_ne_bot
    (G := subgroup) (Subgroup.center subgroup) 2 hdiv
  intro hbot
  apply hinner
  apply Subgroup.map_injective (f := subgroup.subtype) subgroup.subtype_injective
  simpa [omegaOneCenter] using hbot

private theorem centerJoin_initial
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    (ZAt ctx.Γ ctx.criticalPath.a = VAt ctx.Γ ctx.criticalPath.a) ∧
      (∀ neighbor, neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a →
        ZAt ctx.Γ neighbor ≠ ⊥ ∧ ZAt ctx.Γ neighbor ≤ ZAt ctx.Γ ctx.criticalPath.a) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsylow : IsSylowTwoIn T (stabilizer ctx.Γ ctx.criticalPath.a) := by
    rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
    · rw [hedge.1]
      exact ctx.sectionSeven.P1_mem.1.2.1
    · rw [hedge.1]
      exact ctx.sectionSeven.P2_mem.1.2.1
  change IsSylowTwoIn T (ctx.Γ.vertexStabilizer ctx.criticalPath.a) at hsylow
  obtain ⟨_, sylow, hsylow⟩ := hsylow
  have hTp : IsPGroup 2 T := by
    rw [← hsylow]
    exact sylow.isPGroup'.map _
  have hnext := (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
    ctx.commutator_eq).next_center.1
  have hnextMem : ctx.criticalPath.firstStep ∈ neighborhood ctx.Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).2 ctx.criticalPath.firstStep_adj
  have hnextLe : ZAt ctx.Γ ctx.criticalPath.firstStep ≤ ZAt ctx.Γ ctx.criticalPath.a := by
    change _ ≤ ctx.Γ.zAt _
    rw [ctx.Γ.zAt_def]
    apply le_sSup
    exact ⟨sylow, hnext.trans (congrArg omegaOneCenter hsylow.symm)⟩
  have hnextNe : ZAt ctx.Γ ctx.criticalPath.firstStep ≠ ⊥ := by
    rw [show ZAt ctx.Γ ctx.criticalPath.firstStep = omegaOneCenter T from hnext]
    exact centerJoin_omega_nontrivial T hTp ctx.sectionSeven.S_nontrivial
  have hneighbors : ∀ neighbor, neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a →
      ZAt ctx.Γ neighbor ≠ ⊥ ∧ ZAt ctx.Γ neighbor ≤ ZAt ctx.Γ ctx.criticalPath.a := by
    intro neighbor hneighbor
    obtain ⟨element, helement⟩ :=
      (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
        ctx.criticalPath.a hnextMem hneighbor
    have hfix : ctx.Γ.act (element : G) ctx.criticalPath.a = ctx.criticalPath.a := by
      have hdef := ctx.Γ.stabilizer_def ctx.criticalPath.a
      exact (Set.ext_iff.mp hdef (element : G)).mp element.property
    rw [← helement]
    change z ctx.Γ _ ≠ ⊥ ∧ z ctx.Γ _ ≤ z ctx.Γ _
    rw [z_act]
    constructor
    · intro hbot
      apply hnextNe
      apply Subgroup.map_injective (f := (MulAut.conj (element : G)⁻¹).toMonoidHom)
        (MulAut.conj (element : G)⁻¹).injective
      simpa using hbot
    · have hmap := Subgroup.map_mono (f :=
          (MulAut.conj (element : G)⁻¹).toMonoidHom) hnextLe
      rwa [← z_act ctx.Γ (element : G) ctx.criticalPath.a, hfix] at hmap
  refine ⟨le_antisymm ?_ ?_, hneighbors⟩
  · change ctx.Γ.zAt _ ≤ ctx.Γ.vAt _
    rw [ctx.Γ.zAt_def]
    refine sSup_le fun subgroup hsubgroup ↦ ?_
    obtain ⟨otherSylow, rfl⟩ := hsubgroup
    obtain ⟨element, helement⟩ := MulAction.exists_smul_eq
      (ctx.Γ.vertexStabilizer ctx.criticalPath.a) sylow otherSylow
    rw [← helement, centerJoin_sylow_smul, centerJoin_omega_map, hsylow, ← hnext]
    have hle : z ctx.Γ ctx.criticalPath.firstStep ≤ v ctx.Γ ctx.criticalPath.a := by
      change ctx.Γ.zAt _ ≤ ctx.Γ.vAt _
      rw [ctx.Γ.vAt_def]
      exact le_sSup ⟨ctx.criticalPath.firstStep, hnextMem, rfl⟩
    have hnormal := stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a element.property
    have hmap := Subgroup.map_mono (f := (MulAut.conj (element : G)).toMonoidHom) hle
    exact hmap.trans (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormal).le
  · change ctx.Γ.vAt _ ≤ _
    rw [ctx.Γ.vAt_def]
    refine sSup_le fun subgroup hsubgroup ↦ ?_
    obtain ⟨neighbor, hneighbor, rfl⟩ := hsubgroup
    exact (hneighbors neighbor hneighbor).2

/-- The initial-orbit center is exactly the join of its nontrivial neighbor centers. -/
public theorem nine_seven_center_join
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hmiddle : IsConjugateVertex ctx.Γ ctx.criticalPath.a middle) :
    (ZAt ctx.Γ middle = VAt ctx.Γ middle) ∧
      (∀ neighbor, neighbor ∈ Neighborhood ctx.Γ middle →
        ZAt ctx.Γ neighbor ≠ ⊥ ∧ ZAt ctx.Γ neighbor ≤ ZAt ctx.Γ middle) := by
  obtain ⟨element, rfl⟩ := hmiddle
  obtain ⟨hjoin, hneighbors⟩ := centerJoin_initial ctx.toLocalContext
  constructor
  · change z ctx.Γ _ = v ctx.Γ _
    rw [z_act, v_act, show z ctx.Γ ctx.criticalPath.a = v ctx.Γ ctx.criticalPath.a from hjoin]
  · intro neighbor hneighbor
    have hundo : ∀ vertex, ctx.Γ.act element⁻¹ (ctx.Γ.act element vertex) = vertex := by
      intro vertex
      rw [← ctx.Γ.act_mul, mul_inv_cancel, ctx.Γ.act_one]
    have hredo : ctx.Γ.act element (ctx.Γ.act element⁻¹ neighbor) = neighbor := by
      rw [← ctx.Γ.act_mul, inv_mul_cancel, ctx.Γ.act_one]
    have hback : ctx.Γ.act element⁻¹ neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a := by
      apply (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).2
      have hadj := adjacent_act ctx.Γ element⁻¹
        ((SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).1 hneighbor)
      rwa [hundo] at hadj
    obtain ⟨hne, hle⟩ := hneighbors _ hback
    have hcenter : z ctx.Γ neighbor =
        (z ctx.Γ (ctx.Γ.act element⁻¹ neighbor)).map
          (MulAut.conj element⁻¹).toMonoidHom := by
      rw [← z_act, hredo]
    change z ctx.Γ neighbor ≠ ⊥ ∧ z ctx.Γ neighbor ≤ z ctx.Γ _
    rw [hcenter, z_act ctx.Γ element ctx.criticalPath.a]
    constructor
    · intro hbot
      apply hne
      apply Subgroup.map_injective (f := (MulAut.conj element⁻¹).toMonoidHom)
        (MulAut.conj element⁻¹).injective
      exact hbot.trans (Subgroup.map_bot _).symm
    · exact Subgroup.map_mono hle

end Stellmacher.SectionNine
