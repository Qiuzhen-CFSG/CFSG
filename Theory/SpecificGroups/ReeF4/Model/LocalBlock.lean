module

public import Theory.SpecificGroups.ReeF4.Model
public import Theory.SpecificGroups.ReeF4.LocalBlockInput

/-!
# Identifying the local Ree construction with the concrete model

The constructed exceptional endomorphism supplies `canonicalLocalBlockInput`.
Conversely, every `LocalBlockInput` has the same endomorphism, since its values
on all root generators determine it. Its field twist therefore has exactly
the fixed subgroup defining `Model m`, and the comparison equivalence is the
identity on the underlying matrices.

This discharges the construction input used by the local Ree developments.
It also identifies their existential isomorphism interface with direct
isomorphism to `Model m`. Local subgroup and classification conclusions remain
the responsibility of those developments.

Source: the exceptional field twist in GLS3, Theorem 1.15.4(b) and
Theorem 2.2.3(b), with the Ree parameter convention of Aschbacher–Smith,
Remark A.2.4 (`refs/quasithin.pdf`).
-/

public section

namespace ReeF4

/-- The concrete exceptional map supplies the previously conditional local input. -/
noncomputable def canonicalLocalBlockInput (m : ℕ) : LocalBlockInput m where
  hom := exceptionalEndomorphism m
  root_formula := exceptionalEndomorphism_rootGenerator m

@[simp] theorem canonicalLocalBlockInput_hom (m : ℕ) :
    (canonicalLocalBlockInput m).hom = exceptionalEndomorphism m := by rfl

namespace LocalBlockInput

variable {m : ℕ}

/-- There is no choice of exceptional map once its root formulas are fixed. -/
theorem hom_eq_exceptionalEndomorphism (d : LocalBlockInput m) :
    d.hom = exceptionalEndomorphism m :=
  exceptionalEndomorphism_unique m d.hom d.root_formula

theorem twist_toMonoidHom_eq (d : LocalBlockInput m) :
    d.twist.toMonoidHom = reeTwist m := by
  apply splitGroup_hom_ext
  intro r t
  exact (d.twist_root r t).trans (reeTwist_rootGenerator m r t).symm

theorem twist_eq_reeAutomorphism (d : LocalBlockInput m) :
    d.twist = reeAutomorphism m := by
  apply MulEquiv.ext
  intro x
  rw [reeAutomorphism_apply]
  exact DFunLike.congr_fun d.twist_toMonoidHom_eq x

/-- The local construction has exactly the concrete model's fixed subgroup. -/
theorem fixedGroup_eq_fixedSubgroup (d : LocalBlockInput m) :
    d.fixedGroup = fixedSubgroup m := by
  ext x
  rw [mem_fixedGroup, ReeF4.mem_fixedSubgroup]
  change d.twist.toMonoidHom x = x ↔ reeTwist m x = x
  rw [d.twist_toMonoidHom_eq]
  exact Iff.rfl

/-- Identification with the concrete Ree carrier, preserving the ambient matrices. -/
noncomputable def modelEquiv (d : LocalBlockInput m) : d.fixedGroup ≃* Model m :=
  MulEquiv.subgroupCongr d.fixedGroup_eq_fixedSubgroup

@[simp] theorem modelEquiv_coe (d : LocalBlockInput m) (x : d.fixedGroup) :
    (d.modelEquiv x : SplitGroup m) = x.val := by rfl

end LocalBlockInput

/-- The existential local construction interface is equivalent to direct
isomorphism to the concrete model, with its construction premise discharged. -/
theorem exists_localBlockInput_mulEquiv_iff (G : Type*) [Group G] (m : ℕ) :
    (∃ d : LocalBlockInput m, Nonempty (G ≃* d.fixedGroup)) ↔
      Nonempty (G ≃* Model m) := by
  constructor
  · rintro ⟨d, ⟨e⟩⟩
    exact ⟨e.trans d.modelEquiv⟩
  · rintro ⟨e⟩
    exact ⟨canonicalLocalBlockInput m,
      ⟨e.trans (canonicalLocalBlockInput m).modelEquiv.symm⟩⟩

end ReeF4
