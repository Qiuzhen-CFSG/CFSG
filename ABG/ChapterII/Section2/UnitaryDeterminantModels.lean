module
public import ABG.Basic
public import Theory.SpecificGroups.GL2.DeterminantTwoPower

/-!
# The source determinant filtration of GU2

The source subgroup `SU_m(2,q)` consists of the actual unitary matrices whose
determinants have order dividing `2^m`. This module defines that subgroup by
restricting the general-linear determinant filtration to the existing
`GU2 p n hn`, with its original identity-Gram Hermitian form over
`GF(p^(2n))` and q-Frobenius involution.

The membership equation and order criterion are inherited from the GL2
filtration. Inverse images preserve normality and monotonicity. At level
zero, determinant one identifies the subgroup with the existing special
unitary subgroup; the explicit equivalence preserves the underlying matrix.
Its inverse matrix equation is public for the prescribed unitary central-layer
and determinant-center identifications.
No identification of special unitary and special linear groups is assumed.

Source: Alperin--Brauer--Gorenstein, Chapter II, Section 2, article page 17,
the definitions preceding Lemma 1 (`page-018.tex`), subsequently used in
II.3 Proposition 3. The raw filtration is defined for every level; source
bounds on the level and oddness of q belong to later structural results.
-/

namespace ABG

open Matrix.GeneralLinearGroup

@[expose] public noncomputable def SU2Level (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (m : ℕ) :
    Subgroup (GU2 p n hn) :=
  (determinantTwoPower (GaloisField p (2 * n)) m).comap
    (unitaryForm 2 p n hn).unitarySubgroup.subtype

@[simp] public theorem mem_SU2Level_iff
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (m : ℕ) (A : GU2 p n hn) :
    A ∈ SU2Level p n hn m ↔ det A.val ^ (2 ^ m) = 1 := by
  exact mem_determinantTwoPower m A.val

public theorem mem_SU2Level_iff_orderOf_dvd
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (m : ℕ) (A : GU2 p n hn) :
    A ∈ SU2Level p n hn m ↔ orderOf (det A.val) ∣ 2 ^ m := by
  rw [mem_SU2Level_iff, orderOf_dvd_iff_pow_eq_one]

public instance SU2Level_normal
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) (m : ℕ) :
    (SU2Level p n hn m).Normal := by
  unfold SU2Level
  infer_instance

public theorem SU2Level_mono
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) {a b : ℕ} (hab : a ≤ b) :
    SU2Level p n hn a ≤ SU2Level p n hn b := by
  exact Subgroup.comap_mono (determinantTwoPower_mono hab)

@[simp] public theorem SU2Level_zero
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    SU2Level p n hn 0 =
      (unitaryForm 2 p n hn).specialSubgroup.subgroupOf
        (unitaryForm 2 p n hn).unitarySubgroup := by
  ext A
  change (det A.val ^ (2 ^ 0) = 1) ↔
    A.val ∈ (unitaryForm 2 p n hn).unitarySubgroup ∧ det A.val = 1
  simp only [pow_zero, pow_one, A.property, true_and]

public noncomputable def SU2LevelZeroEquivSpecial
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    SU2Level p n hn 0 ≃* (unitaryForm 2 p n hn).specialSubgroup where
  toFun A := ⟨A.val.val, A.val.property, by
    change det A.val.val = 1
    have h := (mem_SU2Level_iff p n hn 0 A.val).mp A.property
    simpa only [pow_zero, pow_one] using h⟩
  invFun A := ⟨⟨A.val, A.property.1⟩, by
    apply (mem_SU2Level_iff p n hn 0 _).mpr
    simpa only [pow_zero, pow_one] using (show det A.val = 1 from A.property.2)⟩
  left_inv A := rfl
  right_inv A := rfl
  map_mul' A B := rfl

public theorem SU2LevelZeroEquivSpecial_symm_val
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (A : (unitaryForm 2 p n hn).specialSubgroup) :
    ((SU2LevelZeroEquivSpecial p n hn).symm A).val.val = A.val := by rfl

end ABG
