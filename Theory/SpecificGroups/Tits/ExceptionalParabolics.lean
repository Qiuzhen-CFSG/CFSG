module

public import Theory.SpecificGroups.Tits.Atlas1600SylowTwo
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# The two concrete Parrott overgroups of the Atlas Sylow subgroup

Adjoin `r1` and `r8`, respectively, to the certified Sylow two-subgroup.
Their join is the whole Atlas group because these subgroups contain all ten
Parrott generators. Their intersection defines the whole overlap of the
inclusion amalgam. The Sylow subgroup embeds in this overlap.

This module does not yet identify the intersection with the Sylow subgroup,
or calculate either intrinsic two-core. In particular it does not assert the
first local invariant printed in Aschbacher--Smith F.1.12(I)(9). That invariant
needs reconciliation with Parrott's involution-centralizer description:
Parrott (1972), p. 672, uses a core of order 512 and quotient of order 20,
whereas F.1.12(I)(9), printed p. 263, says 1024 and dihedral order ten.

Source: Parrott, *A Characterization of the Tits' Simple Group* (1972),
pp. 672, 683--684; the generator conventions and scan transcription are in
`refs/original/n-group-global/parrott-tits-presentation.md`.
-/

@[expose] public section

namespace Tits.ExceptionalParabolics

open Theory.GroupTheory

/-- The specified Sylow subgroup, with its existing certified marking. -/
abbrev S : Subgroup Atlas1600Group := atlas1600SylowTwoSubgroup

/-- The overgroup obtained by adjoining the first Parrott reflection. -/
def first : Subgroup Atlas1600Group :=
  S ⊔ Subgroup.closure {atlas1600ParrottAssignment .r1}

/-- The overgroup obtained by adjoining the second Parrott reflection. -/
def second : Subgroup Atlas1600Group :=
  S ⊔ Subgroup.closure {atlas1600ParrottAssignment .r8}

/-- The whole overlap, without assuming an unproved intersection calculation. -/
def overlap : Subgroup Atlas1600Group := first ⊓ second

theorem sylow_le_first : S ≤ first := le_sup_left

theorem sylow_le_second : S ≤ second := le_sup_left

theorem sylow_le_overlap : S ≤ overlap :=
  le_inf sylow_le_first sylow_le_second

theorem reflection_mem_first : atlas1600ParrottAssignment .r1 ∈ first := by
  apply (show Subgroup.closure {atlas1600ParrottAssignment .r1} ≤ first from le_sup_right)
  exact Subgroup.subset_closure (Set.mem_singleton _)

theorem reflection_mem_second : atlas1600ParrottAssignment .r8 ∈ second := by
  apply (show Subgroup.closure {atlas1600ParrottAssignment .r8} ≤ second from le_sup_right)
  exact Subgroup.subset_closure (Set.mem_singleton _)

private theorem val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
private theorem val_pow (x : Atlas1600Group) (n : ℕ) : (x ^ n).val = x.val ^ n := rfl

private theorem first_reflection_commutes :
    atlas1600ParrottAssignment .r1 * atlas1600R5 =
      atlas1600R5 * atlas1600ParrottAssignment .r1 := by
  rw [atlas1600R5_eq]
  apply Subtype.ext
  simp only [val_mul, val_pow, atlas1600ParrottAssignment_val]
  apply Equiv.ext
  apply Atlas1600ParrottData.allFin
  set_option maxRecDepth 20000 in
  set_option maxHeartbeats 1600000 in
  decide +kernel

/-- The first overgroup centralizes the specified nonidentity central involution. -/
theorem first_le_centralizer : first ≤ Subgroup.centralizer {atlas1600R5} := by
  apply sup_le
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp atlas1600R5_mem_center_sylowTwo ⟨x, hx⟩)
  · apply (Subgroup.closure_le _).mpr
    rintro x (rfl : x = atlas1600ParrottAssignment .r1)
    exact Subgroup.mem_centralizer_singleton_iff.mpr first_reflection_commutes

/-- The two concrete overgroups generate the entire specified Atlas model. -/
theorem generate : first ⊔ second = ⊤ := by
  apply top_unique
  rw [← atlas1600ParrottAssignment_generates]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i, rfl⟩
  have hs : S ≤ first ⊔ second := sylow_le_first.trans le_sup_left
  cases i with
  | r1 => exact (show first ≤ first ⊔ second from le_sup_left) reflection_mem_first
  | r8 => exact (show second ≤ first ⊔ second from le_sup_right) reflection_mem_second
  | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 =>
    apply hs
    rw [S, atlas1600SylowTwoSubgroup_eq]
    apply Subgroup.subset_closure
    simp

/-- The actual inclusion amalgam of the two overgroups and their intersection. -/
def amalgam : RankTwoAmalgam first overlap second :=
  RankTwoAmalgam.ofSubgroups first overlap second inf_le_left inf_le_right

theorem amalgam_left_injective : Function.Injective amalgam.left :=
  Subgroup.inclusion_injective inf_le_left

theorem amalgam_right_injective : Function.Injective amalgam.right :=
  Subgroup.inclusion_injective inf_le_right

theorem sylow_card : Nat.card S = 2048 := atlas1600SylowTwoSubgroup_card

end Tits.ExceptionalParabolics
