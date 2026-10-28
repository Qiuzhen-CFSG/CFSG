module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput
public import Mathlib.GroupTheory.OrderOfElement

/-!+# Frobenius on a supplied Ree fixed group

The exceptional map squares to entrywise Frobenius, so Frobenius commutes
with the odd exceptional power defining the twist. It therefore restricts
to an automorphism of the actual fixed subgroup. Its order divides the
odd coefficient-field degree `2 * m + 1`.

These statements construct the field automorphisms only. Coverage of arbitrary
automorphisms by inner and field automorphisms is a separate theorem. The
construction is valid also at `m = 0`, where the fixed group is the full Ree
group, not the Tits simple group.

Source: GLS3, §2.5, especially 2.5.1(c) and 2.5.12(d), with the field-size
convention of Aschbacher–Smith, Remark A.2.4 (`refs/quasithin.pdf`, p.33).
-/

@[expose] public section
namespace ReeF4.LocalBlockInput
variable {m : ℕ}

/-- Both maps are powers of the supplied exceptional automorphism. -/
theorem frobenius_commutes_twist (d : LocalBlockInput m) :
    Commute (splitFrobeniusEquiv m : MulAut (SplitGroup m)) d.twist := by
  rw [← d.automorphism_sq, d.twist_eq_pow]
  exact Commute.pow_pow_self d.automorphism 2 (2 * m + 1)

/-- Entrywise Frobenius preserves the actual twist-fixed subgroup. -/
theorem frobenius_mem_fixedGroup (d : LocalBlockInput m) {x : SplitGroup m}
    (hx : x ∈ d.fixedGroup) : splitFrobenius m x ∈ d.fixedGroup := by
  apply (d.mem_fixedGroup _).mpr
  have h := DFunLike.congr_fun (d.frobenius_commutes_twist.eq) x
  change splitFrobenius m (d.twist x) = d.twist (splitFrobenius m x) at h
  rw [(d.mem_fixedGroup x).mp hx] at h
  exact h.symm

/-- Restriction of entrywise Frobenius to the supplied fixed subgroup. -/
noncomputable def fixedFrobeniusHom (d : LocalBlockInput m) :
    d.fixedGroup →* d.fixedGroup :=
  ((splitFrobenius m).comp d.fixedGroup.subtype).codRestrict d.fixedGroup
    (fun x => d.frobenius_mem_fixedGroup x.property)

theorem fixedFrobeniusHom_injective (d : LocalBlockInput m) :
    Function.Injective d.fixedFrobeniusHom := by
  intro x y h
  exact Subtype.ext (splitFrobenius_injective m (congrArg Subtype.val h))

/-- The canonical field automorphism of the supplied Ree fixed group. -/
noncomputable def fieldAutomorphism (d : LocalBlockInput m) : MulAut d.fixedGroup :=
  MulEquiv.ofBijective d.fixedFrobeniusHom
    (Finite.injective_iff_bijective.mp d.fixedFrobeniusHom_injective)

@[simp] theorem fieldAutomorphism_coe (d : LocalBlockInput m) (x : d.fixedGroup) :
    (d.fieldAutomorphism x : SplitGroup m) = splitFrobenius m x := rfl

/-- The field automorphism squares each entry of the defining representation. -/
@[simp] theorem fieldAutomorphism_entry (d : LocalBlockInput m) (x : d.fixedGroup)
    (i j : Theory.AlgebraicGroup.F4Chevalley.BasisIndex) :
    (((d.fieldAutomorphism x : SplitGroup m).val : MatrixCarrier m) i j) =
      (x.val.val : MatrixCarrier m) i j ^ 2 := rfl

theorem fieldAutomorphism_pow_coe (d : LocalBlockInput m) (n : ℕ)
    (x : d.fixedGroup) :
    ((d.fieldAutomorphism ^ n) x : SplitGroup m) =
      ((splitFrobeniusEquiv m : MulAut (SplitGroup m)) ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', MulAut.mul_apply, fieldAutomorphism_coe,
      splitFrobeniusEquiv_apply, ih]

/-- On the fixed group the exceptional automorphism itself is already a field
power. Thus it supplies no additional generator beyond Frobenius there. -/
theorem automorphism_on_fixedGroup (d : LocalBlockInput m) (x : d.fixedGroup) :
    d.automorphism x = ((d.fieldAutomorphism ^ (m + 1)) x : SplitGroup m) := by
  rw [d.fieldAutomorphism_pow_coe]
  have h : d.automorphism * d.twist =
      (splitFrobeniusEquiv m : MulAut (SplitGroup m)) ^ (m + 1) := by
    rw [twist, ← mul_assoc, ← pow_two, d.automorphism_sq, pow_succ']
  have hx := (d.mem_fixedGroup x).mp x.property
  calc
    d.automorphism x = d.automorphism (d.twist x) := congrArg d.automorphism hx.symm
    _ = _ := DFunLike.congr_fun h (x : SplitGroup m)

/-- The coefficient-field degree is a period; exact order is not needed. -/
theorem fieldAutomorphism_period (d : LocalBlockInput m) :
    d.fieldAutomorphism ^ (2 * m + 1) = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [d.fieldAutomorphism_pow_coe, localBlock_frobenius_period]
  rfl

theorem orderOf_fieldAutomorphism_dvd (d : LocalBlockInput m) :
    orderOf d.fieldAutomorphism ∣ 2 * m + 1 :=
  orderOf_dvd_of_pow_eq_one d.fieldAutomorphism_period

theorem odd_orderOf_fieldAutomorphism (d : LocalBlockInput m) :
    Odd (orderOf d.fieldAutomorphism) :=
  Odd.of_dvd_nat ⟨m, rfl⟩ d.orderOf_fieldAutomorphism_dvd

end ReeF4.LocalBlockInput
end
