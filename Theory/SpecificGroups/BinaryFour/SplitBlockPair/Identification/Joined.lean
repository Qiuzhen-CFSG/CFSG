module

public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Identification.Joined.Coordinates
public import Mathlib.GroupTheory.GroupAction.Jordan
/-!
# The joined binary group is A₇

The certified exceptional images of all four generators fix letter 3 in A₈.
Restriction to its complement gives a faithful seven-letter representation of
the literal join. Its elements are even. The column cubic is a three-cycle,
and the product of the two cubics is transitive on the seven letters. Prime
degree makes the action primitive, so Jordan's three-cycle theorem gives the
full alternating image.

The resulting multiplicative equivalence retains its action comparison with
the exceptional A₈ representation, including the exact exterior-square /
deleted-module identity after extending by the fixed letter.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of 14.4.4,
printed p.1007, the GL₄(2) join calculation. The realization of this binary pair
by the ambient source subgroups and the marked PSL₃(2) stabilizer are separate
results; no premise from either is used here.
-/

public section

namespace BinaryFourSplitPair.JoinedIdentification
open BinaryFourSplitPair Equiv

noncomputable def toPerm8 : MulAut E →* Perm (Fin 8) :=
  (alternatingGroup (Fin 8)).subtype.comp toAlt8

theorem joined_fixes_three (g : joined) : toPerm8 g.val 3 = 3 := by
  have h : joined ≤ (MulAction.stabilizer (Perm (Fin 8)) (3 : Fin 8)).comap toPerm8 := by
    apply sup_le
    · apply (Subgroup.closure_le _).mpr
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · change (toAlt8 row).val 3 = 3
        rw [toAlt8_row]
        decide +kernel
      · change (toAlt8 column).val 3 = 3
        rw [toAlt8_column]
        decide +kernel
      · change (toAlt8 columnCubic).val 3 = 3
        rw [toAlt8_columnCubic]
        decide +kernel
    · apply (Subgroup.closure_le _).mpr
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · change (toAlt8 row).val 3 = 3
        rw [toAlt8_row]
        decide +kernel
      · change (toAlt8 column).val 3 = 3
        rw [toAlt8_column]
        decide +kernel
      · change (toAlt8 normalizingCubic).val 3 = 3
        rw [toAlt8_normalizingCubic]
        decide +kernel
  exact h g.property

private def restrictPerm (p : Perm (Fin 8)) (hp : p 3 = 3) : Perm (Fin 7) :=
  (finSuccAboveEquiv (3 : Fin 8)).symm.permCongr
    (p.subtypePerm (fun i => by
      change p i ≠ 3 ↔ i ≠ 3
      rw [← hp, p.injective.ne_iff, hp]))

private theorem restrictPerm_apply (p : Perm (Fin 8)) (hp : p 3 = 3) (i : Fin 7) :
    (3 : Fin 8).succAbove (restrictPerm p hp i) = p ((3 : Fin 8).succAbove i) := by
  exact congrArg Subtype.val
    ((finSuccAboveEquiv (3 : Fin 8)).apply_symm_apply
      (p.subtypePerm (fun i => by
        change p i ≠ 3 ↔ i ≠ 3
        rw [← hp, p.injective.ne_iff, hp]) ((finSuccAboveEquiv (3 : Fin 8)) i)))

/-- Restrict the actual exceptional action to the complement of letter 3. -/
noncomputable def toSeven : joined →* Perm (Fin 7) where
  toFun g := restrictPerm (toPerm8 g.val) (joined_fixes_three g)
  map_one' := by
    apply Equiv.ext
    intro i
    apply Fin.succAbove_right_injective (p := (3 : Fin 8))
    rw [restrictPerm_apply]
    change toPerm8 1 _ = _
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro i
    apply Fin.succAbove_right_injective (p := (3 : Fin 8))
    change (3 : Fin 8).succAbove
        (restrictPerm _ (joined_fixes_three (g * h)) i) =
      (3 : Fin 8).succAbove (restrictPerm _ (joined_fixes_three g)
        (restrictPerm _ (joined_fixes_three h) i))
    rw [restrictPerm_apply, restrictPerm_apply, restrictPerm_apply]
    change toPerm8 (g.val * h.val) ((3 : Fin 8).succAbove i) = _
    rw [map_mul]
    rfl

theorem toSeven_apply (g : joined) (i : Fin 7) :
    (3 : Fin 8).succAbove (toSeven g i) = toPerm8 g.val ((3 : Fin 8).succAbove i) :=
  restrictPerm_apply _ (joined_fixes_three g) i

theorem toSeven_injective : Function.Injective toSeven := by
  intro g h he
  apply Subtype.ext
  apply toAlt8_injective
  apply Subtype.ext
  apply Equiv.ext
  intro i
  by_cases hi : i = 3
  · subst i
    exact (joined_fixes_three g).trans (joined_fixes_three h).symm
  · obtain ⟨j, hj⟩ := (finSuccAboveEquiv (3 : Fin 8)).surjective ⟨i, hi⟩
    have hj' : (3 : Fin 8).succAbove j = i := congrArg Subtype.val hj
    change toPerm8 g.val i = toPerm8 h.val i
    rw [← hj', ← toSeven_apply, ← toSeven_apply, he]

theorem toSeven_even (g : joined) : toSeven g ∈ alternatingGroup (Fin 7) := by
  change Perm.sign ((finSuccAboveEquiv (3 : Fin 8)).symm.permCongr _) = 1
  rw [Perm.sign_permCongr, Perm.sign_subtypePerm]
  · exact (toAlt8 g.val).property
  · intro i hi he
    subst i
    exact hi (joined_fixes_three g)

@[expose] def columnSeven : Perm (Fin 7) := swap 0 1 * swap 1 2
@[expose] def normalizingSeven : Perm (Fin 7) := (swap 0 4 * swap 4 5) * (swap 2 3 * swap 3 6)

theorem toSeven_columnCubic :
    toSeven ⟨columnCubic, columnCubic_mem_joined⟩ = columnSeven := by
  apply Equiv.ext
  intro i
  apply Fin.succAbove_right_injective (p := (3 : Fin 8))
  rw [toSeven_apply]
  change (toAlt8 columnCubic).val _ = _
  rw [toAlt8_columnCubic]
  revert i
  decide +kernel

theorem toSeven_normalizingCubic :
    toSeven ⟨normalizingCubic, normalizingCubic_mem_joined⟩ = normalizingSeven := by
  apply Equiv.ext
  intro i
  apply Fin.succAbove_right_injective (p := (3 : Fin 8))
  rw [toSeven_apply]
  change (toAlt8 normalizingCubic).val _ = _
  rw [toAlt8_normalizingCubic]
  revert i
  decide +kernel

/-- Jordan recognition of the actual seven-letter image. -/
theorem toSeven_range : toSeven.range = alternatingGroup (Fin 7) := by
  apply le_antisymm
  · rintro p ⟨g, rfl⟩
    exact toSeven_even g
  · have hb : columnSeven ∈ toSeven.range := ⟨_, toSeven_columnCubic⟩
    have hc : normalizingSeven ∈ toSeven.range := ⟨_, toSeven_normalizingCubic⟩
    have hbc := toSeven.range.mul_mem hb hc
    have trans : ∀ x y : Fin 7, ∃ k : Fin 7,
        ((columnSeven * normalizingSeven) ^ k.val) x = y := by decide +kernel
    let : MulAction.IsPretransitive toSeven.range (Fin 7) := ⟨fun x y => by
      obtain ⟨k, hk⟩ := trans x y
      exact ⟨⟨_, toSeven.range.pow_mem hbc k.val⟩, hk⟩⟩
    apply Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
      (MulAction.IsPreprimitive.of_prime_card (by norm_num)) _ hb
    rw [columnSeven, swap_comm (0 : Fin 7) 1]
    exact Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
end BinaryFourSplitPair.JoinedIdentification

namespace BinaryFourSplitPair
open JoinedIdentification
/-- The literal subgroup generated by the compatible C₂ × S₃ and A₄ is A₇. -/
noncomputable def joinedEquivAlternating : joined ≃* alternatingGroup (Fin 7) :=
  (MonoidHom.ofInjective toSeven_injective).trans
    (MulEquiv.subgroupCongr toSeven_range)

/-- Seven-letter evaluation agrees with the exceptional eight-letter action. -/
theorem joinedEquivAlternating_action (g : joined) (i : Fin 7) :
    (3 : Fin 8).succAbove ((joinedEquivAlternating g).val i) =
      (toAlt8 g.val).val ((3 : Fin 8).succAbove i) :=
  toSeven_apply g i
/-- Restoring the fixed letter recovers the exact exceptional permutation. -/
theorem joinedEquivAlternating_extendDomain (g : joined) :
    (joinedEquivAlternating g).val.extendDomain (finSuccAboveEquiv (3 : Fin 8)) =
      (toAlt8 g.val).val := by
  apply Equiv.ext
  intro i
  by_cases hi : i = 3
  · subst i
    rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)]
    exact (joined_fixes_three g).symm
  · obtain ⟨j, hj⟩ := (finSuccAboveEquiv (3 : Fin 8)).surjective ⟨i, hi⟩
    have hj' : ((finSuccAboveEquiv (3 : Fin 8)) j).val = i := congrArg Subtype.val hj
    rw [← hj', Equiv.Perm.extendDomain_apply_image]
    exact joinedEquivAlternating_action g j

/-- The final equivalence retains the exterior/deleted-module coordinate comparison. -/
theorem joinedEquivAlternating_orthogonal (g : joined) :
    Atlas.Order20160A8.DeletedEight.orthogonalHom
        ((joinedEquivAlternating g).val.extendDomain (finSuccAboveEquiv (3 : Fin 8))) =
      Atlas.Order20160A8.Exterior.toOrthogonal (toSL g.val) := by
  rw [joinedEquivAlternating_extendDomain]
  exact toAlt8_orthogonal g.val

end BinaryFourSplitPair

