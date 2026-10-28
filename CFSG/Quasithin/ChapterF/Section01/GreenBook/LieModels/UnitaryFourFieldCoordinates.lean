module

public import Theory.FieldTheory.QuadraticFrobeniusTrace
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointLocal

/-!
# Trace coordinates for the stored unitary-four field

We apply the binary quadratic trace theorems to the existing `MatrixField n`
and `fieldConj n`, retaining their n*2 degree convention. For n ≥ 1 the trace
kernel and every fixed-field trace fiber have order q = 2^n.

For an actual point-radical matrix with coordinates x and y, the last unitary
equation is z + σ(z) = σ(x)y + σ(y)x. Translation by xσ(y) identifies these
solutions with the fixed field. The resulting matrices are exactly the
point-radical elements with entries (1,3) = x and (2,3) = y, so there are q
such matrices for every x and y. This supplies the affine-coordinate count
used in the U₄(q) construction of Aschbacher--Smith F.1.12(I)(6), printed
p.263 of `refs/quasithin.pdf`. Sylow maximality and the other source clauses
remain with the group-theoretic assembly.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.FieldCoordinates
open Theory.SpecificGroups.ClassicalUnitary
variable (n : ℕ) (hn : 1 ≤ n)

abbrev trace : MatrixField n →+ MatrixField n := InvolutiveTrace.trace (fieldConj n)

@[simp] theorem trace_apply (x : MatrixField n) :
    trace n x = x + fieldConj n x := rfl

include hn in
theorem traceKernel_card : Nat.card (trace n).ker = 2 ^ n := by
  rw [InvolutiveTrace.ker_eq_fixed]
  exact PointLocal.fixedField_card n hn

include hn in
theorem exists_trace_iff (b : MatrixField n) :
    (∃ x, trace n x = b) ↔ fieldConj n b = b := by
  have hne : ∃ x : MatrixField n, fieldConj n x ≠ x := by
    change ∃ x : GaloisField 2 (n * 2),
      iterateFrobeniusEquiv (GaloisField 2 (n * 2)) 2 n x ≠ x
    rw [Nat.mul_comm n 2]
    exact GaloisField.BinaryQuadratic.conj_nontrivial n (by omega)
  exact InvolutiveTrace.exists_trace_iff (fieldConj n) (fieldConj_involutive n hn) hne b

/-- Each fixed-field trace fiber is an affine copy of the fixed field. -/
def traceFiberEquiv (b : PointLocal.FixedField n) :
    {x : MatrixField n // trace n x = b.val} ≃ PointLocal.FixedField n :=
  InvolutiveTrace.fiberEquivFixed (fieldConj n) b.val
    (Classical.choose ((exists_trace_iff n hn b.val).mpr b.property))
    (Classical.choose_spec ((exists_trace_iff n hn b.val).mpr b.property))

include hn in
theorem traceFiber_card (b : MatrixField n) (hb : fieldConj n b = b) :
    Nat.card {x : MatrixField n // trace n x = b} = 2 ^ n := by
  rw [Nat.card_congr (traceFiberEquiv n hn ⟨b, hb⟩)]
  exact PointLocal.fixedField_card n hn

/-- The upper-right-entry equation in the existing point-radical matrix. -/
abbrev RadicalTraceFiber (x y : MatrixField n) :=
  {z : MatrixField n // z + fieldConj n z = fieldConj n x * y + fieldConj n y * x}

/-- The explicit solution x σ(y) parametrizes the radical's affine trace fiber. -/
def radicalTraceFiberEquiv (x y : MatrixField n) :
    RadicalTraceFiber n x y ≃ PointLocal.FixedField n :=
  InvolutiveTrace.fiberEquivFixed (fieldConj n)
    (fieldConj n x * y + fieldConj n y * x) (x * fieldConj n y) (by
      rw [InvolutiveTrace.trace_apply, map_mul, fieldConj_involutive n hn y]
      ring)

include hn in
theorem radicalTraceFiber_card (x y : MatrixField n) :
    Nat.card (RadicalTraceFiber n x y) = 2 ^ n := by
  rw [Nat.card_congr (radicalTraceFiberEquiv n hn x y)]
  exact PointLocal.fixedField_card n hn

/-- A trace-fiber element supplies the missing unitary equation of an actual SU₄ matrix. -/
def radicalOfTraceFiber (x y : MatrixField n) (z : RadicalTraceFiber n x y) :
    PointLocal.Radical n hn :=
  UnitaryFourPointLocal.radicalOfCoordinates (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn) ⟨x, y, z.val, z.property⟩

theorem radicalOfTraceFiber_matrix (x y : MatrixField n) (z : RadicalTraceFiber n x y) :
    (radicalOfTraceFiber n hn x y z).val.val.val.val =
      !![1, fieldConj n y, fieldConj n x, z.val;
         0, 1, 0, x; 0, 0, 1, y; 0, 0, 0, 1] := rfl

theorem radicalOfTraceFiber_injective (x y : MatrixField n) :
    Function.Injective (radicalOfTraceFiber n hn x y) := by
  intro z w h
  apply Subtype.ext
  exact congrArg (fun a : PointLocal.Radical n hn => a.val.val.val.val 0 3) h

/-- The parametrization covers precisely the matrices with the specified two entries. -/
theorem mem_range_radicalOfTraceFiber (x y : MatrixField n) (g : PointLocal.Radical n hn) :
    g ∈ Set.range (radicalOfTraceFiber n hn x y) ↔
      g.val.val.val.val 1 3 = x ∧ g.val.val.val.val 2 3 = y := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨rfl, rfl⟩
  · intro hg
    obtain ⟨c, rfl⟩ := (UnitaryFourPointLocal.radicalCoordinatesEquiv
      (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)).surjective g
    change c.x = x ∧ c.y = y at hg
    rcases c with ⟨a, b, z, hz⟩
    dsimp only at hg
    rcases hg with ⟨rfl, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩

/-- Exactly q actual point-radical matrices have any prescribed first two coordinates. -/
theorem radical_fixed_coordinates_card (x y : MatrixField n) :
    Nat.card {g : PointLocal.Radical n hn //
      g.val.val.val.val 1 3 = x ∧ g.val.val.val.val 2 3 = y} = 2 ^ n := by
  have hs : {g : PointLocal.Radical n hn |
      g.val.val.val.val 1 3 = x ∧ g.val.val.val.val 2 3 = y} =
      Set.range (radicalOfTraceFiber n hn x y) := by
    ext g
    exact (mem_range_radicalOfTraceFiber n hn x y g).symm
  change Nat.card {g : PointLocal.Radical n hn |
    g.val.val.val.val 1 3 = x ∧ g.val.val.val.val 2 3 = y} = _
  rw [hs, Nat.card_range_of_injective (radicalOfTraceFiber_injective n hn x y)]
  exact radicalTraceFiber_card n hn x y
end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.FieldCoordinates
