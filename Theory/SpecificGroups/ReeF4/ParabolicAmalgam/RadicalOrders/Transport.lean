module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalStructure

/-!
# Transport of the concrete Ree radical

The root radical in `Model m`, the radical inside the local residual, and the
radical inside a `LocalBlockInput` seed have the same elements in the split
matrix carrier. The equivalences below retain those elements and hence
transport any cardinality calculation between these three presentations.

This is the subgroup transport needed for Aschbacher–Smith F.1.12(I)(5),
printed p.263 (PDF p.274) of `refs/quasithin.pdf`. It does not identify the
root radical with the intrinsic two-core or calculate its order.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics

open LargeLocalSeeds Subgroup

/-- The comparison with any specified fixed carrier preserves the split matrices. -/
def standardRadicalEquiv {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    standardRadical d s ≃* radical m s where
  toFun x := ⟨d.modelEquiv x.val, by
    change toSplitGroup m (d.modelEquiv x.val) ∈ splitRadical m s
    rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]
    exact x.property⟩
  invFun x := ⟨d.modelEquiv.symm x.val, by
    change (d.modelEquiv.symm x.val).val ∈ splitRadical m s
    rw [modelEquiv_symm_coe]
    simpa only [radical, mem_comap, toSplitGroup_apply] using x.property⟩
  left_inv x := Subtype.ext (d.modelEquiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext (d.modelEquiv.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (d.modelEquiv.map_mul x.val y.val)

@[simp] theorem standardRadicalEquiv_coe {m : ℕ} (d : LocalBlockInput m) (s : Side)
    (x : standardRadical d s) :
    toSplitGroup m (standardRadicalEquiv d s x) = x.val.val := by
  change toSplitGroup m (d.modelEquiv x.val) = x.val.val
  rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]

/-- Restricting the radical to its containing seed changes only the subtype. -/
def seedRadicalEquiv {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    seedRadical d s ≃* radical m s :=
  (subgroupOfEquivOfLe (standardRadical_le_seed d s)).trans (standardRadicalEquiv d s)

@[simp] theorem seedRadicalEquiv_coe {m : ℕ} (d : LocalBlockInput m) (s : Side)
    (x : seedRadical d s) :
    toSplitGroup m (seedRadicalEquiv d s x) = x.val.val.val := by
  exact standardRadicalEquiv_coe d s _

/-- The same radical, viewed inside the local prime-to-two residual. -/
def localRadicalEquiv (m : ℕ) (s : Side) : localRadical m s ≃* radical m s :=
  subgroupOfEquivOfLe (radical_le_localFactor m s)

@[simp] theorem localRadicalEquiv_coe (m : ℕ) (s : Side)
    (x : localRadical m s) : (localRadicalEquiv m s x).val = x.val.val := rfl

theorem card_standardRadical {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    Nat.card (standardRadical d s) = Nat.card (radical m s) :=
  Nat.card_congr (standardRadicalEquiv d s).toEquiv

theorem card_seedRadical {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    Nat.card (seedRadical d s) = Nat.card (radical m s) :=
  Nat.card_congr (seedRadicalEquiv d s).toEquiv

theorem card_localRadical (m : ℕ) (s : Side) :
    Nat.card (localRadical m s) = Nat.card (radical m s) :=
  Nat.card_congr (localRadicalEquiv m s).toEquiv

end ReeF4.Parabolics
