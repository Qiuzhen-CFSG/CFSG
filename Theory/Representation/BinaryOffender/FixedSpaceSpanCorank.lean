module

public import Theory.Representation.BinaryOffender.FixedSpaceSpan
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# Fixed-space spans indexed by corank

For a nontrivial elementary abelian two-subgroup A, the sum of the fixed
spaces of subgroups of corank at most rank(A) - 1 is precisely the sum of
the fixed spaces of its nonidentity elements. Such subgroups are exactly
the nontrivial subgroups; each contains a cyclic subgroup of order two.

This is the identity following Aschbacher–Smith, Definition H.10.1,
printed p.392, using the construction of Definition E.3.30, printed p.237
(combined manuscript of 1 March 2004). Relative index is taken inside A.
-/

@[expose] public section
namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The binary module version of the corank-generated fixed-space subgroup. -/
noncomputable def corankFixedSpaceSpan (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) (k : ℕ) : Submodule (ZMod 2) V :=
  ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : Nat.log 2 (B.relIndex A) ≤ k), fixedSpace ρ B

variable [Finite G]

/-- Corank at most `rank A - 1` excludes precisely the trivial subgroup. -/
theorem corank_le_rank_sub_one_iff {A B : Subgroup G}
    (hA : IsElementaryTwo A) (hBA : B ≤ A) :
    Nat.log 2 (B.relIndex A) ≤ rank A - 1 ↔ B ≠ ⊥ := by
  let _ : IsElementaryAbelian 2 A := hA.2
  rw [← Subgroup.log_card_sub_log_card_eq_log_relIndex A B hBA]
  change rank A - rank B ≤ rank A - 1 ↔ B ≠ ⊥
  have hpos := hA.rank_pos
  constructor
  · rintro h rfl
    rw [rank_bot] at h
    omega
  · intro hB
    have hposB := (hA.of_le hBA hB).rank_pos
    omega

/-- H.10.1: the corank construction is the sum of element fixed spaces. -/
theorem corankFixedSpaceSpan_rank_sub_one (ρ : Representation (ZMod 2) G V)
    {A : Subgroup G} (hA : IsElementaryTwo A) :
    corankFixedSpaceSpan ρ A (rank A - 1) = fixedSpaceSpan ρ A := by
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hBA => iSup_le fun hc => ?_
    have hB := (corank_le_rank_sub_one_iff hA hBA).mp hc
    obtain ⟨b, hb, hb1⟩ := B.bot_or_exists_ne_one.resolve_left hB
    exact (fixedSpace_antitone ρ (Subgroup.zpowers_le.mpr hb)).trans
      (fixedSpace_le_fixedSpaceSpan ρ (hBA hb) hb1)
  · apply fixedSpaceSpan_le
    intro a ha ha1
    have hle : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
    have hne : Subgroup.zpowers a ≠ ⊥ := by
      intro h
      have ha' : a ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers a
      exact ha1 ha'
    exact le_iSup_of_le (Subgroup.zpowers a) (le_iSup_of_le hle
      (le_iSup_of_le ((corank_le_rank_sub_one_iff hA hle).mpr hne) le_rfl))

end Representation.BinaryOffender
