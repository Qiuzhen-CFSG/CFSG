module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsLocal.Pair
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsLocal.InvariantOvergroups.LocalCore
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.Stabilizers

/-!
# The marked second Tits overgroup from Sylow-stabilizer invariance

The explicit normal two-subgroup of the second Atlas parabolic contains
r5. Transporting it through the marking puts the projection of z into
the local core. Relative invariance then puts z into the actual core of
⟨K₂,S⟩, including when S permutes components. The core-centralizer argument
proves every HeOver clause, in particular nontriviality of that core.

The intrinsic centralizer and normalizer identifications now discharge
both parabolic stabilizers. The marked second-overgroup theorems therefore
require only the local setup, Sylow marking and literal projection. From
the source's inner action we also construct the compatible marking and an
invariant pair with both overgroups in HeOver and the first contained in M.
The separate relative-block obstruction belongs to the final exclusion.

Source: Aschbacher–Smith 1.1.5(3)(a), pp.501–502, and 2.3.9(7), pp.525–526.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The actual overgroup core contains z once intrinsic invariance is supplied. -/
theorem titsSecondOver_z_mem_core_of_sylow_stabilizer
    (h : LocalSetup H L M S z) (e : L ≃* Tits.ParrottGroup)
    (hmark : (((S : Subgroup H).map H.subtype).subgroupOf L).map
      (titsAtlasEquiv e).toMonoidHom = Tits.atlas1600SylowTwoSubgroup)
    (hproj : IsConjugationProjection L z ((titsAtlasEquiv e).symm Tits.atlas1600R5))
    (hsecond : ∀ β : MulAut Tits.Atlas1600Group,
      Tits.atlas1600SylowTwoSubgroup.map β.toMonoidHom = Tits.atlas1600SylowTwoSubgroup →
      Tits.ExceptionalParabolics.second.map β.toMonoidHom = Tits.ExceptionalParabolics.second) :
    z ∈ ((titsSecond e).map L.subtype ⊔ (S : Subgroup H).map H.subtype).pCoreIn 2 := by
  let := h.finite
  apply mem_core_of_projection_core h (titsSecond e)
    ((titsAtlasEquiv e).symm Tits.atlas1600R5)
    (normalizes_pullback_of_stabilizer_invariant (titsAtlasEquiv e) _ _ hmark hsecond) hproj
  change _ ∈ (Tits.ExceptionalParabolics.second.map (titsAtlasEquiv e).symm.toMonoidHom).pCoreIn 2
  rw [← map_pCoreIn_of_ker_isPGroup (titsAtlasEquiv e).symm.toMonoidHom
    (IsPGroup.ker_isPGroup_of_injective (titsAtlasEquiv e).symm.injective)]
  exact mem_map_of_mem _ Tits.RelativeParabolicNormalizers.r5_mem_second_core

/-- Full HeOver membership from the remaining intrinsic stabilizer calculation. -/
theorem titsSecondOver_mem_HeOver_of_sylow_stabilizer
    (h : LocalSetup H L M S z) (e : L ≃* Tits.ParrottGroup)
    (hmark : (((S : Subgroup H).map H.subtype).subgroupOf L).map
      (titsAtlasEquiv e).toMonoidHom = Tits.atlas1600SylowTwoSubgroup)
    (hproj : IsConjugationProjection L z ((titsAtlasEquiv e).symm Tits.atlas1600R5))
    (hsecond : ∀ β : MulAut Tits.Atlas1600Group,
      Tits.atlas1600SylowTwoSubgroup.map β.toMonoidHom = Tits.atlas1600SylowTwoSubgroup →
      Tits.ExceptionalParabolics.second.map β.toMonoidHom = Tits.ExceptionalParabolics.second) :
    (titsSecond e).map L.subtype ⊔ (S : Subgroup H).map H.subtype ∈
      Chapter1.HeOver G (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  apply mem_HeOver_of_mem_core h _ le_sup_right
    (sup_le ((map_subtype_le _).trans h.component_le) (map_subtype_le _))
  exact titsSecondOver_z_mem_core_of_sylow_stabilizer h e hmark hproj hsecond

/-- The marked involution belongs to the actual second-overgroup two-core. -/
theorem titsSecondOver_z_mem_core
    (h : LocalSetup H L M S z) (e : L ≃* Tits.ParrottGroup)
    (hmark : (((S : Subgroup H).map H.subtype).subgroupOf L).map
      (titsAtlasEquiv e).toMonoidHom = Tits.atlas1600SylowTwoSubgroup)
    (hproj : IsConjugationProjection L z ((titsAtlasEquiv e).symm Tits.atlas1600R5)) :
    z ∈ ((titsSecond e).map L.subtype ⊔ (S : Subgroup H).map H.subtype).pCoreIn 2 :=
  titsSecondOver_z_mem_core_of_sylow_stabilizer h e hmark hproj
    Tits.RelativeParabolicNormalizers.second_stabilized

/-- Every HeOver clause holds for the marked second parabolic adjoined to S. -/
theorem titsSecondOver_mem_HeOver
    (h : LocalSetup H L M S z) (e : L ≃* Tits.ParrottGroup)
    (hmark : (((S : Subgroup H).map H.subtype).subgroupOf L).map
      (titsAtlasEquiv e).toMonoidHom = Tits.atlas1600SylowTwoSubgroup)
    (hproj : IsConjugationProjection L z ((titsAtlasEquiv e).symm Tits.atlas1600R5)) :
    (titsSecond e).map L.subtype ⊔ (S : Subgroup H).map H.subtype ∈
      Chapter1.HeOver G (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) :=
  titsSecondOver_mem_HeOver_of_sylow_stabilizer h e hmark hproj
    Tits.RelativeParabolicNormalizers.second_stabilized

/-- Nontriviality concerns the actual overgroup core, not just the model core. -/
theorem titsSecondOver_core_ne_bot
    (h : LocalSetup H L M S z) (e : L ≃* Tits.ParrottGroup)
    (hmark : (((S : Subgroup H).map H.subtype).subgroupOf L).map
      (titsAtlasEquiv e).toMonoidHom = Tits.atlas1600SylowTwoSubgroup)
    (hproj : IsConjugationProjection L z ((titsAtlasEquiv e).symm Tits.atlas1600R5)) :
    ((titsSecond e).map L.subtype ⊔ (S : Subgroup H).map H.subtype).pCoreIn 2 ≠ ⊥ :=
  (titsSecondOver_mem_HeOver h e hmark hproj).2.1

/-- The source inner action constructs the invariant pair and both HeOver memberships.
Only N_S(L) is required to preserve the parabolics; S may permute components. -/
theorem tits_exists_pair_of_inner
    (h : LocalSetup H L M S z) (e : L ≃* Tits.ParrottGroup)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ∃ (e' : L ≃* Tits.ParrottGroup)
      (d : InvariantPair L ((S : Subgroup H).map H.subtype)),
      d.left = titsFirst e' ∧ d.right = titsSecond e' ∧
      IsConjugationProjection L z ((titsAtlasEquiv e').symm Tits.atlas1600R5) ∧
      (((S : Subgroup H).map H.subtype).subgroupOf L).map
        (titsAtlasEquiv e').toMonoidHom = Tits.atlas1600SylowTwoSubgroup ∧
      d.leftOver ≤ M ∧
      d.leftOver ∈ Chapter1.HeOver G
        (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) ∧
      d.rightOver ∈ Chapter1.HeOver G
        (((S : Subgroup H).map H.subtype : Subgroup G) : Set G) ∧
      z ∈ d.rightOver.pCoreIn 2 := by
  obtain ⟨e', d, hl, hr, hproj, hmark, hleft, heleft⟩ :=
    tits_exists_pair_of_sylow_stabilizers h e α hα hinner
      Tits.RelativeParabolicNormalizers.first_stabilized
      Tits.RelativeParabolicNormalizers.second_stabilized
  refine ⟨e', d, hl, hr, hproj, hmark, hleft, heleft, ?_, ?_⟩
  · simpa only [InvariantPair.rightOver, hr] using
      titsSecondOver_mem_HeOver h e' hmark hproj
  · simpa only [InvariantPair.rightOver, hr] using
      titsSecondOver_z_mem_core h e' hmark hproj

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
