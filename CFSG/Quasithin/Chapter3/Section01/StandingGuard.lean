module
public import CFSG.Quasithin.Chapter3.Defs
public import CFSG.Quasithin.Chapter1.Section01
public import Mathlib.GroupTheory.Sylow
/-!
# The standing two-maximal-local guard for Section 3.1

After Theorem 2.1.1 the source assumes that the fixed Sylow two-subgroup is
contained in at least two maximal two-local subgroups. For a selected maximal
local `M`, the useful form is an actual maximal two-local outside `M`. This
file makes the conversion to the literal `HStar` definition explicit; it does
not assert Theorem 3.1.8 itself.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A maximal two-local overgroup of `T` that is outside the selected `M`.
This is the local form of the standing assumption after Theorem 2.1.1. -/
def HasMaximalOutside (T : Sylow 2 G) (M : Subgroup G) : Prop :=
  ∃ H : Subgroup G, IsMaximalTwoLocal H ∧ (T : Subgroup G) ≤ H ∧ ¬ H ≤ M

/-- A maximal outside two-local is an `HStar` member after finite minimal descent. -/
theorem exists_HStar_of_hasMaximalOutside
    {T : Sylow 2 G} {M : Subgroup G} (h : HasMaximalOutside T M) :
    ∃ H : Subgroup G, H ∈ HStar (T : Subgroup G) M := by
  classical
  rcases h with ⟨H, hH, hTH, hHM⟩
  let S : Set (Subgroup G) :=
    {Y | Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ M}
  have hHS : H ∈ S := by
    refine ⟨⟨Chapter1.mem_H_of_isTwoLocal hH.1, ?_⟩, ?_⟩
    · exact hTH
    · exact hHM
  obtain ⟨K, hK⟩ := (Set.toFinite S).exists_minimalFor id S ⟨H, hHS⟩
  exact ⟨K, hK⟩

omit [Finite G] in
/-- Two distinct maximal two-locals containing `T` give the outside guard for
one of them. This is the form obtained directly from the post-2.1.1 source
standing assumption. -/
theorem hasMaximalOutside_of_two_distinct
    {T : Sylow 2 G} {M N : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hN : IsMaximalTwoLocal N)
    (_hTM : (T : Subgroup G) ≤ M) (hTN : (T : Subgroup G) ≤ N)
    (hMN : N ≠ M) : HasMaximalOutside T M :=
  ⟨N, hN, hTN, fun hle => hMN (hN.eq_of_le hM.1 hle)⟩

end CFSG.Quasithin.Chapter3
