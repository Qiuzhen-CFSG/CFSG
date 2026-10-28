module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Sylow
public import Theory.SpecificGroups.PSL5Two.TwoRank
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankNonabelianCube
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The two-rank of PSL₅(2)

The genuine binary Sylow subgroup is the stabilizer of the standard full
flag. Projection to its middle three coordinates has the nonabelian
unitriangular group of order eight as target, of two-rank at most two.

In the projection kernel, the first row and last column give six additive
coordinates. Matrix commutation makes the image of an elementary subgroup
self-orthogonal for their nondegenerate row-column pairing. Its dimension
is at most three; the remaining upper-right corner contributes at most
one more binary coordinate. Thus the kernel has two-rank at most four,
and the full Sylow has two-rank at most six. The actual projective-to-linear
equivalence transports this bound to PSL₅(2). The existing 2-by-3 block
embedding supplies equality.

Source application: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of G.9.3, printed p.356 (PDF p.367). This proves the inner-group bound;
the graph-automorphism contribution is a separate assertion.
-/

open Subgroup Theory.GroupTheory
open BinaryLinear.OuterCyclic
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
open scoped IsMulCommutative
local instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5))
    DFunLike.coe_injective

namespace Theory.SpecificGroups.PSL5Two.Upper

@[ext] private structure Middle where
  a : ZMod 2
  b : ZMod 2
  c : ZMod 2
  deriving Fintype, DecidableEq
private instance : One Middle := ⟨⟨0, 0, 0⟩⟩
private instance : Mul Middle := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩⟩
private instance : Inv Middle := ⟨fun x => ⟨x.a, x.b, x.c + x.a * x.b⟩⟩
@[simp] private theorem Middle.mul_a (x y : Middle) : (x * y).a = x.a + y.a := rfl
@[simp] private theorem Middle.mul_b (x y : Middle) : (x * y).b = x.b + y.b := rfl
@[simp] private theorem Middle.mul_c (x y : Middle) : (x * y).c = x.c + y.c + x.a * y.b := rfl
private instance : Group Middle where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

private theorem middle_rank : primeRank 2 Middle ≤ 2 := by
  apply primeRank_le_two_of_nonabelian_card_cube
  · rw [Nat.card_eq_fintype_card]; decide
  · intro h
    let := h
    have h' := congrArg Middle.c (mul_comm (⟨1,0,0⟩ : Middle) ⟨0,1,0⟩)
    exact (by decide : (1 : ZMod 2) ≠ 0) h'

private noncomputable abbrev mat (x : standardBorel) := matrix (x : LinearGroup 5)

private theorem mat_shape (x : standardBorel) : mat x =
    !![1, mat x 0 1, mat x 0 2, mat x 0 3, mat x 0 4;
       0, 1, mat x 1 2, mat x 1 3, mat x 1 4;
       0, 0, 1, mat x 2 3, mat x 2 4;
       0, 0, 0, 1, mat x 3 4;
       0, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact standardBorel_diagonal x.property _ |
      exact (mem_standardBorel_iff _).mp x.property (by decide)

private theorem mat_mul (x y : standardBorel) : mat (x * y) = mat x * mat y := by
  simp only [mat, matrix, Subgroup.coe_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul]

private theorem mat_one : mat 1 = 1 := by
  simp only [mat, matrix, Subgroup.coe_one, map_one, Matrix.SpecialLinearGroup.coe_one]

private noncomputable def middle : standardBorel →* Middle where
  toFun x := ⟨mat x 1 2, mat x 2 3, mat x 1 3⟩
  map_one' := by
    apply Middle.ext <;> change mat 1 _ _ = 0 <;> simp [mat_one]
  map_mul' x y := by
    apply Middle.ext <;>
      change mat (x * y) _ _ = _
    all_goals
      rw [mat_mul, mat_shape x, mat_shape y]
      simp [Matrix.mul_apply, Fin.sum_univ_succ]
      ring

private theorem ker_entries (x : middle.ker) :
    mat x 1 2 = 0 ∧ mat x 2 3 = 0 ∧ mat x 1 3 = 0 := by
  have h : middle x.val = 1 := x.property
  exact ⟨congrArg Middle.a h, congrArg Middle.b h, congrArg Middle.c h⟩

private abbrev Six := (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)

private def pairForm : LinearMap.BilinForm (ZMod 2) Six where
  toFun x := {
    toFun := fun y => x.1 0 * y.2 0 + x.1 1 * y.2 1 + x.1 2 * y.2 2 +
      x.2 0 * y.1 0 + x.2 1 * y.1 1 + x.2 2 * y.1 2
    map_add' := by intros; simp; ring
    map_smul' := by intros; simp; ring }
  map_add' := by intros; apply LinearMap.ext; intro y; simp; ring
  map_smul' := by intros; apply LinearMap.ext; intro y; simp; ring

private theorem pairForm_nondegenerate : pairForm.Nondegenerate := by
  constructor <;> intro x hx <;> apply Prod.ext <;> funext i <;> fin_cases i
  all_goals first
    | simpa [pairForm, Pi.single_apply] using hx (0, Pi.single 0 1)
    | simpa [pairForm, Pi.single_apply] using hx (0, Pi.single 1 1)
    | simpa [pairForm, Pi.single_apply] using hx (0, Pi.single 2 1)
    | simpa [pairForm, Pi.single_apply] using hx (Pi.single 0 1, 0)
    | simpa [pairForm, Pi.single_apply] using hx (Pi.single 1 1, 0)
    | simpa [pairForm, Pi.single_apply] using hx (Pi.single 2 1, 0)

private noncomputable def outside : middle.ker →* Multiplicative Six where
  toFun x := Multiplicative.ofAdd
    (![mat x 0 1, mat x 0 2, mat x 0 3], ![mat x 1 4, mat x 2 4, mat x 3 4])
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp [mat_one]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      change mat (x.val * y.val) _ _ = mat x.val _ _ + mat y.val _ _
    all_goals
      rw [mat_mul, mat_shape x.val, mat_shape y.val]
      simp [Matrix.mul_apply, Fin.sum_univ_succ, (ker_entries x).1, (ker_entries x).2.1,
        (ker_entries x).2.2, (ker_entries y).1, (ker_entries y).2.1, (ker_entries y).2.2, add_comm]

private theorem outside_ext (x y : middle.ker) (h : outside x = outside y)
    (hc : mat x 0 4 = mat y 0 4) : x = y := by
  have h01 := congrArg (fun z : Multiplicative Six => z.toAdd.1 0) h
  have h02 := congrArg (fun z : Multiplicative Six => z.toAdd.1 1) h
  have h03 := congrArg (fun z : Multiplicative Six => z.toAdd.1 2) h
  have h14 := congrArg (fun z : Multiplicative Six => z.toAdd.2 0) h
  have h24 := congrArg (fun z : Multiplicative Six => z.toAdd.2 1) h
  have h34 := congrArg (fun z : Multiplicative Six => z.toAdd.2 2) h
  change mat x 0 1 = mat y 0 1 at h01
  change mat x 0 2 = mat y 0 2 at h02
  change mat x 0 3 = mat y 0 3 at h03
  change mat x 1 4 = mat y 1 4 at h14
  change mat x 2 4 = mat y 2 4 at h24
  change mat x 3 4 = mat y 3 4 at h34
  apply Subtype.ext
  apply Subtype.ext
  apply matrix_injective
  change mat x.val = mat y.val
  rw [mat_shape x.val, mat_shape y.val]
  simp only [(ker_entries x).1, (ker_entries x).2.1, (ker_entries x).2.2,
    (ker_entries y).1, (ker_entries y).2.1, (ker_entries y).2.2,
    h01, h02, h03, h14, h24, h34, hc]

private theorem outside_orthogonal (x y : middle.ker) (h : x * y = y * x) :
    pairForm (outside x).toAdd (outside y).toAdd = 0 := by
  have hh := congrArg (fun z : middle.ker => mat z 0 4) h
  change mat (x.val * y.val) 0 4 = mat (y.val * x.val) 0 4 at hh
  rw [mat_mul, mat_mul, mat_shape x.val, mat_shape y.val] at hh
  simp only [Matrix.mul_apply, Fin.sum_univ_succ] at hh
  simp at hh
  change mat x 0 1 * mat y 1 4 + mat x 0 2 * mat y 2 4 + mat x 0 3 * mat y 3 4 +
    mat x 1 4 * mat y 0 1 + mat x 2 4 * mat y 0 2 + mat x 3 4 * mat y 0 3 = 0
  linear_combination (norm := ring_nf) hh
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]

private theorem kernel_rank : primeRank 2 middle.ker ≤ 4 := by
  apply (primeRank_le_iff_elementary_card_le middle.ker).mpr
  intro E hE
  let := hE
  let a : Additive E →+ Six := {
    toFun x := (outside x.toMul.val).toAdd
    map_zero' := by change (outside 1).toAdd = 0; rw [map_one]; rfl
    map_add' x y := by
      change (outside (x.toMul.val * y.toMul.val)).toAdd = _
      rw [map_mul]; rfl }
  let l := a.toZModLinearMap 2
  have hiso : l.range ≤ pairForm.orthogonal l.range := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact outside_orthogonal y.toMul.val x.toMul.val
      (congrArg Subtype.val (mul_comm y.toMul x.toMul))
  have hdim := Submodule.finrank_mono hiso
  rw [LinearMap.BilinForm.finrank_orthogonal pairForm_nondegenerate] at hdim
  have hsix : Module.finrank (ZMod 2) Six = 6 := by
    simp [Six, Module.finrank_prod]
  rw [hsix] at hdim
  have hthree : Module.finrank (ZMod 2) l.range ≤ 3 := by omega
  have hcard : Nat.card l.range ≤ 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hthree)
  let enc : E → l.range × ZMod 2 := fun x =>
    (⟨(outside x.val).toAdd, ⟨Additive.ofMul x, rfl⟩⟩, mat x.val 0 4)
  have hinj : Function.Injective enc := by
    intro x y h
    apply Subtype.ext
    apply outside_ext
    · apply Multiplicative.toAdd.injective
      exact congrArg (fun z : l.range × ZMod 2 => z.1.val) h
    · exact congrArg Prod.snd h
  have hc := Nat.card_le_card_of_injective enc hinj
  rw [Nat.card_prod, Nat.card_zmod] at hc
  calc
    Nat.card E ≤ Nat.card l.range * 2 := hc
    _ ≤ 8 * 2 := Nat.mul_le_mul_right 2 hcard
    _ = 2 ^ 4 := by decide

end Upper

/-- The actual binary full-flag Sylow subgroup has two-rank at most six. -/
public theorem standardBorel_primeRank_le_six : primeRank 2 standardBorel ≤ 6 := by
  have h := primeRank_le_ker_add (p := 2) Upper.middle
  have hk := Upper.kernel_rank
  have hm := Upper.middle_rank
  omega

/-- The unconditional intrinsic upper bound on the concrete projective carrier. -/
public theorem primeRank_le_six :
    primeRank 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) ≤ 6 := by
  rw [primeRank_equiv 2 (projectiveEquivLinear (by decide : 0 < 5))]
  rw [Sylow.primeRank_eq standardSylow]
  exact standardBorel_primeRank_le_six

/-- The upper bound is attained by the six-entry upper-right block. -/
public theorem primeRank_eq_six :
    primeRank 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) = 6 :=
  Nat.le_antisymm primeRank_le_six six_le_primeRank

end Theory.SpecificGroups.PSL5Two
