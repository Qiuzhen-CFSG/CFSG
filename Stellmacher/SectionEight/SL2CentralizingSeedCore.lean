module

public import Stellmacher.SectionEight.SL2CentralizingSeedDisjoint

/-!
# A centralizing SL₂(2) seed modulo a normal subgroup

If `P/N` is SL₂(2), a two-subgroup `V` centralizes the normal two-subgroup
`N` modulo `W`, and `V ∩ N ≤ W`, then its `P`-conjugate closure also
intersects `N` inside `W`.

Pass to `P/W`, descend the supplied quotient homomorphism, and apply the
centralizing-seed disjointness theorem. The intersection transport uses
`W ≤ N`; no preservation of arbitrary intersections under images is assumed.
This is the abstract algebra input for Stellmacher (8.6)(1), printed p.41,
without generated graph, core-generation, or equation-one hypotheses.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven
open scoped commutatorElement

universe u

private theorem seed_quotient_model
    {G : Type u} [Group G] (P N W : Subgroup G)
    [normalW : (W.subgroupOf P).Normal]
    (hWN : W ≤ N) (hquot : QuotientIsModel P N SL2Two) :
    ∃ projection : (P ⧸ W.subgroupOf P) →* SL2Two,
      Function.Surjective projection ∧
        projection.ker = (N.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P)) := by
  obtain ⟨projection, hsurj, hker⟩ := hquot
  have hle : W.subgroupOf P ≤ projection.ker := by
    rw [hker]
    intro element helement
    exact hWN helement
  refine ⟨QuotientGroup.lift (W.subgroupOf P) projection hle,
    QuotientGroup.lift_surjective_of_surjective _ projection hsurj hle, ?_⟩
  rw [QuotientGroup.ker_lift, hker]

private theorem seed_quotient_commutator_eq_bot
    {G : Type u} [Group G] (P N V W : Subgroup G)
    [normalW : (W.subgroupOf P).Normal]
    (hcomm : ⁅N, V⁆ ≤ W) :
    ⁅(N.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P)),
      (V.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P))⁆ = ⊥ := by
  apply le_bot_iff.mp
  rw [← Subgroup.map_commutator, Subgroup.map_le_iff_le_comap]
  rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
  apply Subgroup.commutator_le.mpr
  intro first hfirst second hsecond
  exact hcomm (Subgroup.commutator_mem_commutator hfirst hsecond)

private theorem seed_quotient_intersection_eq_bot
    {G : Type u} [Group G] (P N V W : Subgroup G)
    [normalW : (W.subgroupOf P).Normal]
    (hWN : W ≤ N) (hinter : V ⊓ N ≤ W) :
    (V.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P)) ⊓
      (N.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P)) = ⊥ := by
  apply le_bot_iff.mp
  rintro element ⟨⟨seed, hseed, rfl⟩, core, hcore, heq⟩
  have hdiff : seed⁻¹ * core ∈ W.subgroupOf P := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (W.subgroupOf P)) (seed⁻¹ * core) = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  have hseedN : (seed : G) ∈ N := by
    have hprod := N.mul_mem hcore (N.inv_mem (hWN hdiff))
    simpa only [map_mul, map_inv, mul_inv_rev,
      inv_inv, mul_inv_cancel_left, Subgroup.subtype_apply] using hprod
  exact (QuotientGroup.eq_one_iff _).mpr (hinter ⟨hseed, hseedN⟩)

private theorem seed_closure_core_le_of_quotient_disjoint
    {G : Type u} [Group G] (P N V W : Subgroup G)
    [normalW : (W.subgroupOf P).Normal] (hVP : V ≤ P)
    (hdisjoint : Stellmacher.conjugateClosure
      ((V.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P))) ⊤ ⊓
      (N.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P)) = ⊥) :
    Stellmacher.conjugateClosure V P ⊓ N ≤ W := by
  let projection := QuotientGroup.mk' (W.subgroupOf P)
  let imageClosure := Stellmacher.conjugateClosure ((V.subgroupOf P).map projection) ⊤
  have hclosure : Stellmacher.conjugateClosure V P ≤
      (imageClosure.comap projection).map P.subtype := by
    rw [Stellmacher.conjugateClosure, Subgroup.closure_le]
    rintro element ⟨actor, seed, rfl⟩
    let seedP : P := ⟨seed, hVP seed.property⟩
    refine ⟨actor * seedP * actor⁻¹, ?_, rfl⟩
    change projection (actor * seedP * actor⁻¹) ∈ imageClosure
    apply Subgroup.subset_closure
    refine ⟨⟨projection actor, Subgroup.mem_top _⟩,
      ⟨projection seedP, Subgroup.mem_map_of_mem projection seed.property⟩, ?_⟩
    simp only [map_mul, map_inv]
  intro element hmem
  obtain ⟨elementP, hprojected, helement⟩ := hclosure hmem.1
  change (elementP : G) = element at helement
  have hcore : elementP ∈ N.subgroupOf P := by
    change (elementP : G) ∈ N
    rw [helement]
    exact hmem.2
  have hzero : projection elementP = 1 := by
    have hboth : projection elementP ∈ imageClosure ⊓
        (N.subgroupOf P).map projection :=
      ⟨hprojected, Subgroup.mem_map_of_mem projection hcore⟩
    rw [hdisjoint] at hboth
    exact hboth
  have hW : elementP ∈ W.subgroupOf P := (QuotientGroup.eq_one_iff _).mp hzero
  change (elementP : G) ∈ W at hW
  rwa [helement] at hW

public theorem sl2_centralizing_seed_closure_core_le
    {G : Type u} [Group G] [Finite G]
    (P N V W : Subgroup G)
    (hN : NormalIn N P) (hNtwo : IsPGroup 2 N)
    (hquot : Later.QuotientIsModel P N SL2Two)
    (hVP : V ≤ P) (hVtwo : IsPGroup 2 V)
    (hW : NormalIn W P) (hWN : W ≤ N)
    (hcomm : ⁅N, V⁆ ≤ W) (hinter : V ⊓ N ≤ W) :
    Stellmacher.conjugateClosure V P ⊓ N ≤ W := by
  let _ : (W.subgroupOf P).Normal := hW.2
  let _ : (N.subgroupOf P).Normal := hN.2
  let projection := QuotientGroup.mk' (W.subgroupOf P)
  let core := (N.subgroupOf P).map projection
  let seed := (V.subgroupOf P).map projection
  let _ : core.Normal := hN.2.map projection (QuotientGroup.mk'_surjective _)
  have hcoretwo : IsPGroup 2 core := hNtwo.comap_subtype.map projection
  have hseedtwo : IsPGroup 2 seed := hVtwo.comap_subtype.map projection
  obtain ⟨model, hsurj, hker⟩ := seed_quotient_model P N W hWN hquot
  have hdisjoint := sl2_centralizing_seed_closure_disjoint core seed hcoretwo
    model hsurj hker hseedtwo (seed_quotient_commutator_eq_bot P N V W hcomm)
    (seed_quotient_intersection_eq_bot P N V W hWN hinter)
  exact seed_closure_core_le_of_quotient_disjoint P N V W hVP hdisjoint

end Stellmacher.SectionEight
