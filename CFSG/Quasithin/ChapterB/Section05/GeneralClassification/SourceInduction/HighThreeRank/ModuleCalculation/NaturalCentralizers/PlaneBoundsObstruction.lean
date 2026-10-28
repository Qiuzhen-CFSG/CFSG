module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.OffenderPlane
public import Theory.Representation.TwoDimensionalOddOrder
/-!
# The incompatible cubic fixed-codimension premise

The published `OffenderPlaneBounds` asks for fixed codimension two on a
space of dimension at most two. A nonzero binary module for a two-group
always has a nonzero fixed vector. Consequently this contract cannot be
constructed for an actual best offender in the finite source action.

This diagnoses the intermediate interface, not B.5.7: the source's
codimension-two assertion concerns the component moved space U. The cubic
moved plane has fixed codimension one under its nontrivial involution.
The valid `OffenderPlaneConclusion` and the ambient centralizer assembly
remain usable once a producer proves the endgame without the bad premise.
Source: Aschbacher–Smith, B.5.7, printed p.106, final two sentences.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

private theorem fixedCodim_lt_finrank (ρ : Representation (ZMod 2) G V)
    [Module.Finite (ZMod 2) V] [Nontrivial V]
    (A : Subgroup G) (hA : IsPGroup 2 A) :
    fixedCodim ρ A < Module.finrank (ZMod 2) V := by
  have hc : ringChar (ZMod 2) = 2 := ringChar.eq (ZMod 2) 2
  obtain ⟨v, hv, hfix⟩ := Representation.pGroup_fix_nonzero_vector (F := ZMod 2)
    (by rw [hc]; decide) (by simpa only [hc] using hA) (ρ.comp A.subtype)
  have hvf : v ∈ fixedSpace ρ A := hfix
  have hn : Nontrivial (fixedSpace ρ A) := by
    apply Submodule.nontrivial_iff_ne_bot.mpr
    intro he
    apply hv
    simpa only [he, Submodule.mem_bot] using hvf
  have hp : 0 < Module.finrank (ZMod 2) (fixedSpace ρ A) := Module.finrank_pos_iff.mpr hn
  have hs := fixedCodim_add_finrank ρ A
  omega

/-- The old endgame contract cannot be constructed: its cubic fixed codimension
is two while its whole cubic moved space has dimension at most two. Every
nonzero binary module for a two-group has a nonzero fixed vector. -/
theorem not_offenderPlaneBounds {K : GroupClass.{u}}
    (ρ : Representation (ZMod 2) G V) (hyp : FFHypothesis K ρ)
    {L A : Subgroup G} (hA : IsBestOffender ρ A)
    (m : SymmetricMovedModel ρ L A) : ¬ Nonempty (OffenderPlaneBounds ρ m) := by
  rintro ⟨b⟩
  let := hyp.finite_module
  let σ : Representation (ZMod 2) G (moved ρ (pCore 3 G)) :=
    (normalMoved ρ (pCore 3 G)).toRepresentation
  have hs := fixedCodim_add_finrank σ A
  have hd : fixedCodim σ A = 2 := b.cubic_fixedCodim_eq hA
  have hp : 0 < Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) := by
    change fixedCodim σ A + _ = Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) at hs
    omega
  let : Nontrivial (moved ρ (pCore 3 G)) :=
    Module.finrank_pos_iff.mp hp
  let := hA.1.2
  have hlt := fixedCodim_lt_finrank σ A (IsElementaryAbelian.isPGroup 2 A)
  have hu := b.plane_bound hA
  change fixedCodim σ A < Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) at hlt
  omega
end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
