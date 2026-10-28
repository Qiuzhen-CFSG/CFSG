module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow

/-!
# A fixed radical candidate inside the first Hall--Janko parabolic

Four short words in the unchanged Sylow generators specify a subgroup of
the literal centralizer `Seed.l₁`. The membership proofs use only the checked
containment of that Sylow subgroup. Its normality, order, quaternion--dihedral
factors, and quotient actions remain separate calculations.

The words were found by computing the two-core of the centralizer in the
ATLAS degree-100 group and then expressing its generators in the fixed
Sylow alphabet. The retained permutations and words are in
`FirstParabolic/source/`. This discovery is not a proof of the core identity.
Source: Aschbacher--Smith F.1.12(I)(10)--(11), printed p.263.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open Theory.GroupTheory Seed

/-- The shared first-radical words, in the alphabet `Seed.sGenerator`. -/
def radicalWord : Fin 4 → List (Fin 7) := ![[5, 0], [5, 4], [3], [4, 3]]

def radicalGenerator (i : Fin 4) : Carrier := evalWord sGenerator (radicalWord i)

/-- A concrete generated subgroup, without a two-core assumption. -/
def radical : Subgroup Carrier := Subgroup.closure (Set.range radicalGenerator)

theorem radicalGenerator_mem_s (i : Fin 4) : radicalGenerator i ∈ s := by
  have hw (w : List (Fin 7)) : evalWord sGenerator w ∈ s := by
    induction w with
    | nil => exact s.one_mem
    | cons j w ih => exact s.mul_mem (Subgroup.subset_closure ⟨j, rfl⟩) ih
  exact hw _

theorem radical_le_s : radical ≤ s := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact radicalGenerator_mem_s i

theorem radical_le_l₁ : radical ≤ l₁ :=
  radical_le_s.trans SecondParabolic.s_le_l₁

/-- The same radical candidate included in the concrete permutation extension. -/
def outerRadical : Subgroup Extension := radical.map intoExtension

theorem outerRadical_le_outerL : outerRadical ≤ outerL 0 :=
  Subgroup.map_mono radical_le_l₁

theorem outerRadical_le_l₁s : outerRadical ≤ l₁s :=
  outerRadical_le_outerL.trans le_sup_left

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
