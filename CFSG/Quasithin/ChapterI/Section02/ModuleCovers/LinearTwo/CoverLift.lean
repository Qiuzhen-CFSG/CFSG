module

public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.LinearTwo
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center.CoverLift

/-!
# I.2.3 for the natural SL₂ module

The explicit orthogonal three-space is identified with the actual universal
binary L-cover over the original natural projection. The construction and
root-space calculations apply to every finite characteristic-two field of
order 2ⁿ, n > 1, including order four. Central quotients need only be binary
vector spaces.

This supplies `RankOneCoverTheorem` to the existing Chapter E application,
removing that earlier-source premise from its centralizer conclusion. The
statement concerns universal L-covers; the ambient G-cover audit remains with
the parent I.2.3 assembly.

The natural action uses SL₂ with its actual matrix marking. The characteristic-
two SL₂/PSL₂ equivalence is the one proved in `SL2NaturalH1.projectiveEquiv`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.3(1a,b),(3),
printed p.413/PDF p.424, and its E.6.7 application, printed p.246.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterI.ModuleCovers.LinearTwo
open Representation Representation.OneCohomology Representation.SL2OrthogonalCover
namespace Application
open CFSG.Quasithin.ChapterE.Section06.L2Torus
universe u v
variable (F : Type u) [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- A genuine orthogonal realization of the cohomological universal binary cover. -/
theorem orthogonalUniversalCover (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    Nonempty (CoverLift.OrthogonalUniversalCover F) := by
  obtain ⟨e,he,hp⟩ := universal_equiv (F := F) n hn hF
  exact ⟨{
    action := action (F := F)
    form := form (F := F)
    nondegenerate := form_nondegenerate (F := F)
    preserves := form_invariant (F := F)
    fixed_radical := fixed_radical (F := F)
    radical_dimension := radical_dimension (F := F)
    projection := projection (F := F)
    projection_surjective := projection_surjective (F := F)
    projection_kernel := projection_kernel (F := F)
    equivalence := e
    intertwining := he
    over_natural := hp }⟩

/-- The entire earlier-source rank-one cover interface, with no realization,
dimension or extra cohomology premise. -/
theorem rankOneCoverTheorem (n : ℕ) : CoverLift.RankOneCoverTheorem.{u,v} F n := by
  intro hn hF
  refine ⟨orthogonalUniversalCover F n hn hF, ?_⟩
  intro W _ _ _ σ p hp
  exact cover_root_geometry n hn hF p hp

variable {F} {L : Type v} [Group L] [Finite L] {B : Subgroup L}

/-- Actual application to the marked block: the former I.2.3 hypothesis is discharged. -/
theorem rootLine_le_centralizer
    (hshort : ChapterC.IsShort L) (a : MarkedBlockModel L B F)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    a.rootLine ≤ Subgroup.centralizer (S : Set L) :=
  CoverLift.rootLine_le_centralizer_of_I23 hshort a hn hF (rankOneCoverTheorem F n) S hS

/-- The full centralizer equality in the original Chapter E consumer. -/
theorem blockU_centralizer_sylow_eq_rootLine
    (hshort : ChapterC.IsShort L) (a : MarkedBlockModel L B F)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    ChapterC.blockU L ⊓ Subgroup.centralizer (S : Set L) = a.rootLine :=
  CoverLift.blockU_centralizer_sylow_eq_rootLine_of_I23 hshort a hn hF (rankOneCoverTheorem F n) S hS
end Application
end CFSG.Quasithin.ChapterI.ModuleCovers.LinearTwo
