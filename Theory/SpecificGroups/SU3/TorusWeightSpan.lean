module

public import Theory.FieldTheory.MultiplicativeSpan
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.TorusWeights

/-!
# Unitary torus weights over prime-power fixed fields

The actual first-coordinate torus weight is k/conj(k)². Its kernel consists
of cube roots of unity, so its image has at least q elements when the matrix
field has q² elements and q > 2. The multiplicative-span theorem therefore
proves additive generation of the full matrix field, with no primality
assumption on q. An additive equivalence that is multiplicative on these
weights is consequently multiplicative everywhere.

This is the field-recovery step for binary PSU₃ automorphism coverage.
The existing prime-order proof cannot be reused by simply replacing p with q:
a proper additive subgroup can have more than q elements. Here the span is
a subfield because the generating weights form a multiplicative subgroup.

Source: Steinberg, Theorem36, steps(3)–(4), refs/KGroup/GLS3/Chapter2St1.tex.
-/

public section
open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.TorusWeightSpan
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- The actual torus weights span every quadratic finite field with q > 2,
including arbitrary binary prime powers. -/
theorem additive_span {q : ℕ} (hq : 2 < q) (hcard : Nat.card E = q ^ 2) :
    AddSubgroup.closure (Set.range (fun k : Eˣ => (torusWeight J k : E))) = ⊤ := by
  have hr : q ≤ Nat.card (torusWeight J).range := by
    have hprod := (torusWeight J).ker.card_mul_index
    rw [Subgroup.index_ker, Nat.card_units, hcard] at hprod
    have hk := torusWeight_kernel_card_le_three J
    by_contra h
    have hle : q ^ 2 - 1 ≤ 3 * (q - 1) := by
      rw [← hprod]
      exact Nat.mul_le_mul hk (by omega)
    have hq1 : 1 ≤ q := by omega
    have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
    have hx := Nat.sub_add_cancel hq2
    have hy := Nat.sub_add_cancel hq1
    nlinarith
  have hs : Set.range (fun k : Eˣ => (torusWeight J k : E)) =
      Set.range (fun u : (torusWeight J).range => (u.val : E)) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨torusWeight J k, ⟨k, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨u, hu⟩, rfl⟩
      obtain ⟨k, rfl⟩ := hu
      exact ⟨k, rfl⟩
  rw [hs]
  exact FiniteField.MultiplicativeSpan.additive_span_eq_top_of_large_units
    (torusWeight J).range hcard hr

/-- Multiplicativity on the actual torus weights suffices on the whole field. -/
theorem mul_eq_of_weights {q : ℕ} (hq : 2 < q) (hcard : Nat.card E = q ^ 2)
    (f : E ≃+ E)
    (hweight : ∀ k : Eˣ, ∀ x : E, f ((torusWeight J k : E) * x) =
      f (torusWeight J k : E) * f x) (a x : E) : f (a * x) = f a * f x := by
  have h (a : E)
      (ha : a ∈ AddSubgroup.closure (Set.range (fun k : Eˣ => (torusWeight J k : E)))) :
      ∀ x, f (a * x) = f a * f x := by
    induction ha using AddSubgroup.closure_induction with
    | mem a ha =>
      obtain ⟨k, rfl⟩ := ha
      exact hweight k
    | zero => simp
    | add a b _ _ ha hb =>
      intro x
      simp only [add_mul, map_add, ha x, hb x]
    | neg a _ ha =>
      intro x
      simp only [neg_mul, map_neg, ha x]
  exact h a (by rw [additive_span J hq hcard]; exact AddSubgroup.mem_top a) x

end BenderSuzuki.MatrixGroups.HermitianForm.TorusWeightSpan
