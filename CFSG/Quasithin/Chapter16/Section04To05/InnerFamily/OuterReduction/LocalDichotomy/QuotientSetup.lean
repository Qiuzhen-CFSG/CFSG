module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.Setup
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Fixed groups and centralizer images in the quotient

Conjugation by r induces the actual automorphism of L/O₂(L). Its full fixed
group can be larger than the image of the fixed group in L. The two subgroups
are retained separately, with their inclusion proved by equivariance.

An image of index two forces the full fixed group to be nonperfect, which
is the input to the inspection of 16.1.4–5 on printed p.1190. No index or
missing-involution assertion is assumed to hold by these definitions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1190, between (+) and (!).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy
open ComponentTransfer.Intrinsic
variable {G : Type*} [Group G] {L : Subgroup G} {r : G}

/-- The full fixed group on the actual quotient L/O₂(L). -/
abbrev quotientFixed (hn : r ∈ normalizer (L : Set G)) : Subgroup (L ⧸ pCore 2 L) :=
  (quotientAction hn).fixedSubgroup

/-- The image of C_L(r) in L/O₂(L), distinct from the full fixed group. -/
def centralizerImage (hn : r ∈ normalizer (L : Set G)) : Subgroup (L ⧸ pCore 2 L) :=
  (action hn).fixedSubgroup.map (QuotientGroup.mk' (pCore 2 L))

/-- A fixed point upstairs maps to a fixed point downstairs. -/
theorem centralizerImage_le (hn : r ∈ normalizer (L : Set G)) :
    centralizerImage hn ≤ quotientFixed hn := by
  rintro x ⟨y, hy, rfl⟩
  change _ ∈ (quotientAction hn).fixedSubgroup
  rw [MulAut.mem_fixedSubgroup, quotientAction_apply]
  exact congrArg (QuotientGroup.mk' (pCore 2 L))
    ((MulAut.mem_fixedSubgroup _ _).mp hy)

/-- The source image as a subgroup of the full quotient fixed group. -/
def imageInFixed (hn : r ∈ normalizer (L : Set G)) : Subgroup (quotientFixed hn) :=
  (centralizerImage hn).subgroupOf (quotientFixed hn)

/-- Index two of the image rules out a perfect quotient fixed group. This
is the restriction used when inspecting the earlier automorphism tables. -/
theorem quotientFixed_not_perfect (hn : r ∈ normalizer (L : Set G))
    (hi : (imageInFixed hn).index = 2) : ¬ Group.IsPerfect (quotientFixed hn) := by
  intro hp
  let : Group.IsPerfect (quotientFixed hn) := hp
  have htop : (imageInFixed hn) = ⊤ := top_le_iff.mp
    (le_of_isPerfect_of_index_eq_two ⊤ (imageInFixed hn) hi)
  rw [htop, index_top] at hi
  omega

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy
