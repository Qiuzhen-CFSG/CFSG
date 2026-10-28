module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# A compatible binary four-dimensional pair

Coordinates are the entries (13, 14, 23, 24) of the elementary abelian
middle radical in the upper unitriangular group of degree four. The row
involution adds the second row to the first; the column involution and
column cubic act on both rows. The other cubic cycles the common four-group's
three involutions and fixes the marked central vector (0,1,0,0).

The short words bc and bcbcc have orders seven and five. Their powers are
checked on sixteen vectors, so the generated image has both prime divisors
without an enumeration of GL₄(2). This module does not identify the generated
group by its order or assume a comparison with A₇.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the compatible
local images in the proof of 14.4.4, printed p.1007. Their realization by
actual ambient subgroups is a separate split-block calculation.
-/

namespace BinaryFourSplitPair
public abbrev V := Fin 4 → ZMod 2
public abbrev E := Multiplicative V

@[expose] public def rowFun (v : V) : V := ![v 0 + v 2, v 1 + v 3, v 2, v 3]
@[expose] public def columnFun (v : V) : V := ![v 0, v 0 + v 1, v 2, v 2 + v 3]
@[expose] public def columnCubicFun (v : V) : V := ![v 1, v 0 + v 1, v 3, v 2 + v 3]
@[expose] public def normalizingCubicFun (v : V) : V := ![v 3, v 1 + v 3, v 2, v 0 + v 3]

@[expose] public def involution (f : V → V) (hi : ∀ v, f (f v) = v)
    (hm : ∀ v w, f (v + w) = f v + f w) : MulAut E :=
  AddEquiv.toMultiplicative {
    toFun := f, invFun := f, left_inv := hi, right_inv := hi, map_add' := hm }

@[expose] public def cubic (f : V → V) (hi : ∀ v, f (f (f v)) = v)
    (hm : ∀ v w, f (v + w) = f v + f w) : MulAut E :=
  AddEquiv.toMultiplicative {
    toFun := f, invFun := fun v => f (f v), left_inv := hi, right_inv := hi,
    map_add' := hm }

@[expose] public def row : MulAut E := involution rowFun (by decide +kernel) (by decide +kernel)
@[expose] public def column : MulAut E := involution columnFun (by decide +kernel) (by decide +kernel)
@[expose] public def columnCubic : MulAut E := cubic columnCubicFun (by decide +kernel) (by decide +kernel)
@[expose] public def normalizingCubic : MulAut E := cubic normalizingCubicFun (by decide +kernel) (by decide +kernel)

/-- The common four-group, with its actual embedding. -/
@[expose] public def overlap : Subgroup (MulAut E) := Subgroup.closure {row, column}
/-- Row transvection and the full binary column group. -/
@[expose] public def parabolic : Subgroup (MulAut E) := Subgroup.closure {row, column, columnCubic}
/-- The common four-group extended by its specified cycling cubic. -/
@[expose] public def quaternion : Subgroup (MulAut E) := Subgroup.closure {row, column, normalizingCubic}
/-- The marked center vector, corresponding to the (1,4) entry. -/
@[expose] public def point : E := Multiplicative.ofAdd ![0,1,0,0]

public theorem row_sq : row * row = 1 := by
  apply MulEquiv.ext
  decide +kernel
public theorem column_sq : column * column = 1 := by
  apply MulEquiv.ext
  decide +kernel
public theorem row_column_commute : row * column = column * row := by
  apply MulEquiv.ext
  decide +kernel
public theorem columnCubic_cube : columnCubic ^ 3 = 1 := by
  apply MulEquiv.ext
  decide +kernel
public theorem normalizingCubic_cube : normalizingCubic ^ 3 = 1 := by
  apply MulEquiv.ext
  decide +kernel
public theorem normalizingCubic_conj_row :
    normalizingCubic * row * normalizingCubic⁻¹ = column := by
  apply MulEquiv.ext
  decide +kernel
public theorem normalizingCubic_conj_column :
    normalizingCubic * column * normalizingCubic⁻¹ = row * column := by
  apply MulEquiv.ext
  decide +kernel
public theorem quaternion_generators_fix_point :
    row point = point ∧ column point = point ∧ normalizingCubic point = point := by decide +kernel

@[expose] public def joined : Subgroup (MulAut E) := parabolic ⊔ quaternion
@[expose] public def sevenWord : MulAut E := columnCubic * normalizingCubic
@[expose] public def fiveWord : MulAut E := columnCubic * normalizingCubic * columnCubic *
  normalizingCubic * normalizingCubic

public theorem sevenWord_order : orderOf sevenWord = 7 := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply MulEquiv.ext
    decide +kernel
  · intro h
    exact (by decide +kernel : sevenWord point ≠ point) (DFunLike.congr_fun h point)

public theorem fiveWord_order : orderOf fiveWord = 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply MulEquiv.ext
    decide +kernel
  · intro h
    exact (by decide +kernel : fiveWord point ≠ point) (DFunLike.congr_fun h point)

public theorem columnCubic_mem_joined : columnCubic ∈ joined :=
  (show parabolic ≤ joined from le_sup_left)
    (Subgroup.subset_closure (by simp))

public theorem normalizingCubic_mem_joined : normalizingCubic ∈ joined :=
  (show quaternion ≤ joined from le_sup_right)
    (Subgroup.subset_closure (by simp))

public theorem sevenWord_mem_joined : sevenWord ∈ joined :=
  joined.mul_mem columnCubic_mem_joined normalizingCubic_mem_joined

public theorem fiveWord_mem_joined : fiveWord ∈ joined :=
  joined.mul_mem (joined.mul_mem (joined.mul_mem
    (joined.mul_mem columnCubic_mem_joined normalizingCubic_mem_joined)
      columnCubic_mem_joined) normalizingCubic_mem_joined) normalizingCubic_mem_joined

public theorem seven_dvd_card_joined : 7 ∣ Nat.card joined := by
  simpa only [sevenWord_order] using joined.orderOf_dvd_natCard sevenWord_mem_joined

public theorem five_dvd_card_joined : 5 ∣ Nat.card joined := by
  simpa only [fiveWord_order] using joined.orderOf_dvd_natCard fiveWord_mem_joined

public theorem card_E : Nat.card E = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide


end BinaryFourSplitPair
