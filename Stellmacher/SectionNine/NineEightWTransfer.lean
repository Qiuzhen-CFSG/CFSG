module

public import Stellmacher.SectionNine.NineEightNeighborhood
public import Stellmacher.SectionNine.NineTenExtraction
public import Stellmacher.SectionNine.NineTwoAmbientCentralizerCommutator
public import Stellmacher.SectionFiveToSeven.ResidualTransport

/-!
# Residual transfer in the opening of Stellmacher (9.8)

The residual is transitive on every vertex neighborhood. A commutator bound
modulo the middle core therefore transfers subgroup containment between
neighboring stabilizers. The ambient (7.7)(a) bound transports to every
initial-orbit vertex, in particular the penultimate vertex, without moving
Hypothesis Two from H to the embedded graph group.

For W at a neighbor of the first step, these results prove terminal
containment from the penultimate center-product identity. That identity is
an explicit premise here, not a conclusion. The module does not assert the
subsequent W-based (7.8)/(7.6)(d) extraction or the bound b ≤ 3.

Source: Stellmacher, printed p.55 / PDF p.45, first paragraph of (9.8),
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement

universe u

private theorem fixes_iff_mem
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (actor : G) (vertex : Γ.Vertex) :
    actor ∈ GAt Γ vertex ↔ Γ.act actor vertex = vertex := by
  exact Set.ext_iff.mp (Γ.stabilizer_def vertex) actor

public theorem nine_eight_residual_transitivity
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (vertex : Γ.Vertex) :
    IsActionTransitiveOn Γ (EAt Γ vertex) (neighborhood Γ vertex) := by
  intro left right hleft hright
  let edge := GAt Γ vertex ⊓ GAt Γ left
  let sylow := sylowTwoAmbient edge (default : Sylow 2 edge)
  have hsylow := ((lemma_seven_three h Γ).sylow_and_core vertex left hleft
    (default : Sylow 2 edge)).1
  have hres : EAt Γ vertex = twoResidualIn (GAt Γ vertex) := Γ.twoResidualAt_def vertex
  have hjoin : sylow ⊔ EAt Γ vertex = GAt Γ vertex := by
    rw [sup_comm, hres]
    exact twoResidualIn_sup_sylow hsylow
  have hnormal : GAt Γ vertex ≤ Subgroup.normalizer (EAt Γ vertex) := by
    rw [hres]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le _)).mp
      (twoResidualIn_normal _)
  obtain ⟨actor, hactor⟩ := (lemma_seven_one h Γ).local_transitivity vertex hleft hright
  have hmem : (actor : G) ∈ sylow ⊔ EAt Γ vertex := hjoin.symm ▸ actor.property
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hsylow.1.trans hnormal)] at hmem
  obtain ⟨fixed, hfixed, residual, hresidual, heq⟩ := hmem
  refine ⟨⟨residual, hresidual⟩, ?_⟩
  have hfixedEdge : fixed ∈ edge := by
    obtain ⟨element, _, rfl⟩ := hfixed
    exact element.property
  have hfix := (fixes_iff_mem Γ fixed left).mp hfixedEdge.2
  rw [← heq, Γ.act_mul, hfix] at hactor
  exact hactor

public theorem nine_eight_stabilizer_transfer_of_commutator
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (middle left right : Γ.Vertex)
    (hleft : left ∈ neighborhood Γ middle)
    (hright : right ∈ neighborhood Γ middle) (W : Subgroup G)
    (hW : W ≤ GAt Γ left) (hcomm : ⁅W, EAt Γ middle⁆ ≤ QAt Γ middle) :
    W ≤ GAt Γ right := by
  obtain ⟨actor, hactor⟩ := nine_eight_residual_transitivity h Γ middle hleft hright
  have hcore : QAt Γ middle ≤ GAt Γ left :=
    ((lemma_seven_three h Γ).sylow_and_core middle left hleft default).2.2
  rw [Subgroup.commutator_comm] at hcomm
  intro element helement
  have hconj : (actor : G) * element * (actor : G)⁻¹ ∈ GAt Γ left := by
    have hbound := hcore (hcomm (Subgroup.commutator_mem_commutator actor.property helement))
    have hmul := (GAt Γ left).mul_mem hbound (hW helement)
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hmul
  rw [← hactor]
  change element ∈ stabilizer Γ (Γ.act (actor : G) left)
  rw [stabilizer_act, conjugateBy, Subgroup.mem_map_equiv]
  simpa only [MulAut.conj_symm_apply, inv_inv] using hconj

private theorem centralizer_map_equiv
    {G : Type u} [Group G] (equiv : G ≃* G) (subgroup : Subgroup G) :
    (Subgroup.centralizer (subgroup : Set G)).map equiv.toMonoidHom =
      Subgroup.centralizer (subgroup.map equiv.toMonoidHom : Set G) := by
  apply le_antisymm (Subgroup.map_centralizer_le_centralizer_image _ _)
  intro element helement
  refine ⟨equiv.symm element, ?_, equiv.apply_symm_apply element⟩
  rw [Subgroup.mem_centralizer_iff] at helement
  change ∀ member ∈ subgroup, member * equiv.symm element = equiv.symm element * member
  intro member hmember
  apply equiv.injective
  simpa only [map_mul, equiv.apply_symm_apply] using
    helement (equiv member) (Subgroup.mem_map_of_mem _ hmember)

public theorem nine_eight_initial_orbit_centralizer_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex) :
    ⁅Subgroup.centralizer (ZAt ctx.Γ vertex : Set G), EAt ctx.Γ vertex⁆ ≤
      QAt ctx.Γ vertex := by
  obtain ⟨actor, rfl⟩ := horbit
  have hbound := (Subgroup.commutator_mono le_rfl
    (show EAt ctx.Γ ctx.criticalPath.a ≤ EAt ctx.Γ ctx.criticalPath.a ⊔
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) from le_sup_left)).trans
        (nine_two_initial_centralizer_commutator ctx)
  have hres : EAt ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a) =
      (EAt ctx.Γ ctx.criticalPath.a).map (MulAut.conj actor⁻¹).toMonoidHom := by
    change ctx.Γ.twoResidualAt _ = (ctx.Γ.twoResidualAt _).map _
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoResidualAt_def]
    change twoResidualIn (stabilizer ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a)) = _
    rw [stabilizer_act, conjugateBy, twoResidualIn_map_equiv]
    rfl
  change ⁅Subgroup.centralizer (z ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a) : Set G),
    EAt ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a)⁆ ≤
      q ctx.Γ (ctx.Γ.act actor ctx.criticalPath.a)
  rw [z_act, hres, q_act, ← centralizer_map_equiv, ← Subgroup.map_commutator]
  exact Subgroup.map_mono hbound

public theorem nine_eight_penultimate_centralizer_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    let penultimate := ctx.criticalPath.path
      ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    ⁅Subgroup.centralizer (ZAt ctx.Γ penultimate : Set G), EAt ctx.Γ penultimate⁆ ≤
      QAt ctx.Γ penultimate := by
  obtain ⟨actor, hactor, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  exact nine_eight_initial_orbit_centralizer_commutator ctx _ ⟨actor, hactor⟩

public theorem nine_eight_first_orbit_center_centralizes
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (vertex : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep vertex) :
    GAt ctx.Γ vertex ≤ Subgroup.centralizer (ZAt ctx.Γ vertex : Set G) := by
  have hfirst : GAt ctx.Γ ctx.criticalPath.firstStep ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.firstStep : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    change z ctx.Γ ctx.criticalPath.firstStep ≤ _
    rw [(lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).next_center.2]
    exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)
  obtain ⟨actor, rfl⟩ := horbit
  change stabilizer ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep) ≤
    Subgroup.centralizer (z ctx.Γ (ctx.Γ.act actor ctx.criticalPath.firstStep) : Set G)
  rw [stabilizer_act, conjugateBy, z_act, ← centralizer_map_equiv]
  exact Subgroup.map_mono hfirst

public theorem nine_eight_neighborhood_le_terminal_of_center_product
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hproduct : ZAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) =
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 2, by omega⟩) ⊔
        ZAt ctx.Γ ctx.criticalPath.a')
    (vertex : ctx.Γ.Vertex)
    (hvertex : vertex ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep) :
    GeneratedNeighborhoodV ctx.Γ vertex ≤ GAt ctx.Γ ctx.criticalPath.a' := by
  let cp := ctx.criticalPath
  let previous := cp.path ⟨cp.length - 2, by omega⟩
  let middle := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hlong : 4 < cp.length := by
    have hfive := nine_ten_length_ge_five ctx.toLocalContext hb
    change 5 ≤ cp.length at hfive
    omega
  have hleft : previous ∈ neighborhood ctx.Γ middle := by
    apply (mem_neighborhood_iff_adjacent ctx.Γ).mpr
    apply ctx.Γ.adjacent_symm
    have hedge := cp.path_adj ⟨cp.length - 2, by omega⟩
    have hindex : (⟨cp.length - 2, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hindex] at hedge
    exact hedge
  have hright : cp.a' ∈ neighborhood ctx.Γ middle := by
    apply (mem_neighborhood_iff_adjacent ctx.Γ).mpr
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hlast : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hlast, cp.path_end] at hedge
    exact hedge
  have hW := nine_eight_neighborhood_le_preterminal ctx.toLocalContext hlong vertex hvertex
  have hpreviousOrbit : IsConjugateVertex ctx.Γ cp.firstStep previous := by
    obtain ⟨alignment, _, halign⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven ctx.Γ cp ctx.commutator_eq
    obtain ⟨actor, hactor⟩ := nine_eight_residual_transitivity ctx.sectionSeven ctx.Γ
      middle hright hleft
    refine ⟨alignment * (actor : G), ?_⟩
    rw [ctx.Γ.act_mul, halign]
    exact hactor
  have hcentralLeft := hW.trans
    (nine_eight_first_orbit_center_centralizes ctx.toLocalContext previous hpreviousOrbit)
  have hcentralRight := nine_eight_neighborhood_centralizes_terminal_center
    ctx.toLocalContext hlong hcontain vertex hvertex
  have hcentral : GeneratedNeighborhoodV ctx.Γ vertex ≤
      Subgroup.centralizer (ZAt ctx.Γ middle : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    rw [hproduct]
    exact sup_le (Subgroup.le_centralizer_iff.mp hcentralLeft)
      (Subgroup.le_centralizer_iff.mp hcentralRight)
  exact nine_eight_stabilizer_transfer_of_commutator ctx.sectionSeven ctx.Γ
    middle previous cp.a' hleft hright _ hW
      ((Subgroup.commutator_mono hcentral le_rfl).trans
        (nine_eight_penultimate_centralizer_commutator ctx))

end Stellmacher.SectionNine
