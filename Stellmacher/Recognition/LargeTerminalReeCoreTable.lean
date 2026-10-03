module

public import Stellmacher.Recognition.LargeTerminalReeRootSeed
public import Stellmacher.Recognition.LargeTerminalFiveFixedConjugateGeometry
public import Stellmacher.Recognition.LargeTerminalOuterCosetGeometry
public import Stellmacher.Recognition.LargeTerminalReeFrameConstruction
public import Theory.SpecificGroups.ReeTwo.CoreFrame

/-!
# Checking a Ree frame in the actual terminal core

The fixed root centralizes the elementary derived layer. Every forced tail
root is a commutator in the actual core, whose derived subgroup is that same
layer. Thus all tail squares and commutators in Shinoda's table are automatic,
as are commutators with the designated omega-central involution.

The remaining input is a four-element frame with the normalized square map,
upper commutators and pairing. The lower frame-construction module supplies
such a frame from the terminal geometry, and this module verifies and
assembles the full table. No frame element is required to belong to the
residual.

Source: Thompson VI, pp.629–630, and Shinoda (1975), (2.3), pp.81–82.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

/-- The elementary tail and the central root require no extra coordinate data.
The four frame elements may lie anywhere in the actual second core. -/
public theorem LargeTerminalContext.ree_core_relations_of_frame
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (t z : twoCoreIn ctx.second)
    (hz : orderOf (z : G) = 2)
    (hgen : zpowers (z : G) = omegaOneCenter (S : Subgroup G))
    (htA : (t : G) ∈ centralizer (A : Set G)) (htsq : t ^ 2 = z)
    (a : Fin 4 → twoCoreIn ctx.second)
    (hframe : ReeTwo.FrameCoordinates a t z) :
    ReeTwo.CoreRelations (ReeTwo.frameRoots a t z) := by
  let Q := twoCoreIn ctx.second
  let D := DerivedAmbient ctx.firstResidual
  have hDmap : (commutator Q).map Q.subtype = D := ctx.second_core_derived_eq
  have hDQ : D ≤ Q := hDmap ▸ map_subtype_le _
  have hDsub : D.subgroupOf Q = commutator Q := by
    rw [← hDmap]
    exact comap_map_eq_self_of_injective Q.subtype_injective _
  let _ : IsElementaryAbelian 2 D := ctx.derived_residual_elementary
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsElementaryAbelian 2 (D.subgroupOf Q) := IsElementaryAbelian.subgroupOf hDQ
  apply ReeTwo.coreRelations_frameRoots_of_elementary (D.subgroupOf Q)
    (by rw [hDsub]) a t z hframe
  · have htD := ctx.five_fixed_centralizes_derived A hA hAN hfixed t t.property htA
    apply mem_centralizer_iff.mpr
    intro d hd
    apply Subtype.ext
    exact mem_centralizer_iff.mp htD d hd
  · apply mem_center_iff.mpr
    intro q
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      (ctx.residual_normalizer_le_involution_centralizer z hz hgen
        (ctx.second_le_residual_normalizer (twoCoreIn_le ctx.second q.property)))
  · exact htsq
  · apply Subtype.ext
    change (z : G) ^ 2 = 1
    rw [← hz]
    exact pow_orderOf_eq_one (z : G)

/-- Verification retains the actual last root and the actual five-fixed
cyclic subgroup, rather than merely producing an abstract isomorphic core. -/
public theorem LargeTerminalContext.exists_ree_core_roots_of_frame
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (t z : twoCoreIn ctx.second)
    (hz : orderOf (z : G) = 2)
    (hgen : zpowers (z : G) = omegaOneCenter (S : Subgroup G))
    (htA : (t : G) ∈ centralizer (A : Set G)) (htsq : t ^ 2 = z)
    (htgen : zpowers (t : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (a : Fin 4 → twoCoreIn ctx.second)
    (hframe : ReeTwo.FrameCoordinates a t z) :
    ∃ x : ReeTwo.CoreRoot → twoCoreIn ctx.second,
      ReeTwo.CoreRelations x ∧ (x 9 : G) = z ∧
      zpowers (x 2 : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G) := by
  exact ⟨ReeTwo.frameRoots a t z,
    ctx.ree_core_relations_of_frame A hA hAN hfixed t z hz hgen htA htsq a hframe,
    rfl, htgen⟩

/-- The terminal order-4096 geometry supplies the actual ten Ree roots.

The designated involution and the cyclic five-fixed subgroup are retained
literally in the resulting root map; no abstract replacement of the core is
used. -/
public theorem LargeTerminalContext.exists_ree_core_roots_of_cyclic
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : twoCoreIn ctx.second) (hz : orderOf (z : G) = 2)
    (hgen : zpowers (z : G) = omegaOneCenter (S : Subgroup G)) :
    ∃ x : ReeTwo.CoreRoot → twoCoreIn ctx.second,
      ReeTwo.CoreRelations x ∧ (x 9 : G) = z ∧
      zpowers (x 2 : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G) := by
  obtain ⟨t, a, htA, htsq, htgen, hframe⟩ :=
    ctx.exists_ree_frame_of_cyclic hS A hA hAP hAN hcard hcyc hfixed z hz hgen
  exact ctx.exists_ree_core_roots_of_frame A hA hAN hfixed t z hz hgen htA htsq
    htgen a hframe

/-- The ambient-element form of the terminal root construction. Membership
of the designated involution in the core follows from its central-line
property, so it is not an extra input. -/
public theorem LargeTerminalContext.exists_ree_core_roots_at_generator_of_cyclic
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ x : ReeTwo.CoreRoot → twoCoreIn ctx.second,
      ReeTwo.CoreRelations x ∧ (x 9 : G) = z ∧
      zpowers (x 2 : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G) := by
  have hzR : z ∈ ctx.firstResidual := by
    apply (show CenterAmbient ctx.firstResidual ≤ ctx.firstResidual from map_subtype_le _)
    rw [ctx.first_residual_center_eq_omegaOneCenter, ← hgen]
    exact mem_zpowers z
  have hRQ : ctx.firstResidual ≤ twoCoreIn ctx.second :=
    ctx.derived_centralizer_supplement.1 ▸ le_sup_right
  exact ctx.exists_ree_core_roots_of_cyclic hS A hA hAP hAN hcard hcyc hfixed
    ⟨z, hRQ hzR⟩ hz hgen

end Stellmacher.Recognition
