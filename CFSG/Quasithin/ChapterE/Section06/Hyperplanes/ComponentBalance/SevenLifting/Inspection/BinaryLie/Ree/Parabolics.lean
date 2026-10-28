module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import Theory.GroupTheory.PerfectCyclicSylowProjection
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear

/-!
# Seven-component obstructions in the full Ree parabolics

Both A₇ and its perfect central three-cover have three-rank at least two.
A perfect subgroup embedded in a full Ree parabolic has trivial projection
to the complementary torus. The two-group radical leaves its three-subgroups
embedded in the rank-one Levi factor, whose odd Sylow subgroups are cyclic.

The linear-side projection is constructed in the imported matrix geometry.
For the Suzuki side the required projection and its two-group kernel remain
explicit inputs. These are full parabolics, including the complementary torus;
no component membership in a larger overgroup is asserted.

Source: Aschbacher–Smith, E.6.18, printed p.252, and F.1.12(I)(5), printed
p.263 of `refs/quasithin.pdf`; GLS3, Theorem 2.6.5, for the local Levi structure.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
open ReeF4.ConverseParabolics

/-- The proved full linear-parabolic projection excludes both seven models
from every perfect subgroup embedded in that parabolic. -/
theorem ree_linear_no_seven {S : Type*} [Group S] [Finite S]
    {m : ℕ} (hm : 1 ≤ m) (L : Subgroup S) [Group.IsPerfect L]
    (f : L →* parabolic m .linear) (hf : Function.Injective f) : ¬ IsSeven L := by
  intro hseven
  have hr := perfect_threeRank_le_one_of_embedding
    (linearProjectionOfLeviHom (linearFullLeviEmbedding hm))
    (linearProjectionOfLeviHom_ker_isPGroup _ (linearFullLeviEmbedding_injective hm))
    f hf (fun U hU => Matrix.SL2.odd_pGroup_isCyclic_of_injective hU
      (by decide : 3 ≠ 2) U.subtype U.subtype_injective)
  have hl := hseven.two_le_primeRank
  omega

/-- A Suzuki-times-torus projection with two-group kernel suffices for the
second parabolic. Constructing this projection remains a model obligation. -/
theorem ree_suzuki_no_seven_of_projection {S : Type*} [Group S] [Finite S]
    {m : ℕ} (hm : 1 ≤ m)
    (π : parabolic m .suzuki →*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m × (ReeF4.CoefficientField m)ˣ)
    (hker : IsPGroup 2 π.ker)
    (L : Subgroup S) [Group.IsPerfect L]
    (f : L →* parabolic m .suzuki) (hf : Function.Injective f) : ¬ IsSeven L := by
  intro hseven
  have hr := perfect_threeRank_le_one_of_embedding π hker f hf (fun U hU => by
    obtain ⟨P, hUP⟩ := hU.exists_le_sylow
    let : IsCyclic P := BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two
      (by omega : 0 < m) (by decide : 3 ≠ 2) P
    exact Subgroup.isCyclic_of_le hUP)
  have hl := hseven.two_le_primeRank
  omega

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
