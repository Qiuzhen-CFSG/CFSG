module

public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Automorphism-invariant counts on Frattini cosets

A family of automorphism-invariant predicates gives counting functions on the
fibers of a quotient map. Compatible automorphisms preserve these functions.
For a finite p-group, if their stabilizer on the Frattini quotient has p-power
exponent elementwise, the full automorphism group is a p-group by the Burnside
basis-kernel theorem. This extends the power-equation counts to predicates
involving centralizer sizes, without asserting that every profile symmetry lifts.
-/

namespace MonoidHom
variable {G V I : Type*} [Group G] [Group V]

/-- The number of elements satisfying a predicate in a specified fiber. -/
@[expose] public noncomputable def predicateFiberCard (π : G →* V)
    (P : G → Prop) (v : V) : ℕ := Nat.card {x : G // π x = v ∧ P x}

/-- Compatible automorphisms preserve fiber counts for invariant predicates. -/
public theorem predicateFiberCard_map (π : G →* V) (P : G → Prop)
    (f : MulAut G) (a : MulAut V) (h : ∀ x, π (f x) = a (π x))
    (hP : ∀ x, P (f x) ↔ P x) (v : V) :
    predicateFiberCard π P (a v) = predicateFiberCard π P v := by
  apply Nat.card_congr
  refine {
    toFun := fun x => ⟨f.symm x, ?_⟩
    invFun := fun x => ⟨f x, ?_⟩
    left_inv := fun x => Subtype.ext (f.apply_symm_apply x)
    right_inv := fun x => Subtype.ext (f.symm_apply_apply x) }
  · constructor
    · apply a.injective
      rw [← h, f.apply_symm_apply]
      exact x.property.1
    · exact (hP _).mp (by simpa using x.property.2)
  · exact ⟨by rw [h, x.property.1], (hP _).mpr x.property.2⟩

/-- Invariant fiber counts and the Burnside kernel theorem give a finite
certificate for the full automorphism group of a p-group. -/
public theorem isPGroup_mulAut_of_frattini_predicateFiber [Finite G] {p : ℕ}
    (hG : IsPGroup p G) (π : G →* V) (hπ : Function.Surjective π)
    (hker : π.ker = frattini G) (P : I → G → Prop)
    (hP : ∀ (f : MulAut G) i x, P i (f x) ↔ P i x)
    (cert : ∀ a : MulAut V,
      (∀ i v, predicateFiberCard π (P i) (a v) = predicateFiberCard π (P i) v) →
      ∃ k : ℕ, a ^ (p ^ k) = 1) : IsPGroup p (MulAut G) := by
  let e : (G ⧸ frattini G) ≃* V :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have he (x : G) : e (QuotientGroup.mk' (frattini G) x) = π x := rfl
  let ρ : MulAut G →* MulAut V :=
    (MulAut.congr e).toMonoidHom.comp (Subgroup.quotientAut (frattini G))
  have hρ (f : MulAut G) (x : G) : ρ f (π x) = π (f x) := by
    change e (Subgroup.quotientAut (frattini G) f (e.symm (π x))) = _
    rw [← he x, e.symm_apply_apply, Subgroup.quotientAut_apply_mk, he]
  have hrange : IsPGroup p ρ.range := by
    rintro ⟨a, f, rfl⟩
    obtain ⟨k, hk⟩ := cert (ρ f) (fun i => predicateFiberCard_map π (P i) f
      (ρ f) (fun x => (hρ f x).symm) (hP f i))
    exact ⟨k, Subtype.ext hk⟩
  have hkernel : IsPGroup p ρ.ker := by
    have hEq : ρ.ker = (Subgroup.quotientAut (frattini G)).ker := by
      ext f
      change MulAut.congr e (Subgroup.quotientAut (frattini G) f) = 1 ↔ _
      exact (MulAut.congr e).map_eq_one_iff
    rw [hEq]
    exact Subgroup.isPGroup_quotientAut_frattini_kernel hG
  have ht := hrange.comap_of_ker_isPGroup ρ hkernel
  have htop : ρ.range.comap ρ = ⊤ := by ext f; simp
  rw [htop] at ht
  exact ht.of_surjective (⊤ : Subgroup (MulAut G)).subtype (fun f => ⟨⟨f, trivial⟩, rfl⟩)
end MonoidHom

namespace MulAut
variable {G : Type*} [Group G]

/-- Centralizer cardinality expressed as a count of commuting elements. -/
@[expose] public noncomputable def commutingCard (x : G) : ℕ :=
  Nat.card {y : G // y * x = x * y}

/-- Automorphisms preserve centralizer cardinalities. -/
public theorem commutingCard_apply (f : MulAut G) (x : G) :
    commutingCard (f x) = commutingCard x := by
  apply Nat.card_congr
  refine {
    toFun := fun y => ⟨f.symm y, ?_⟩
    invFun := fun y => ⟨f y, ?_⟩
    left_inv := fun y => Subtype.ext (f.apply_symm_apply y)
    right_inv := fun y => Subtype.ext (f.symm_apply_apply y) }
  · apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using y.property
  · simpa only [map_mul] using congrArg f y.property

/-- A profile test specifies element order, centralizer size, and optionally
the centralizer size of the square. Zero in the third position omits that test. -/
@[expose] public def orderCentralizerTest (t : ℕ × ℕ × ℕ) (x : G) : Prop :=
  orderOf x = t.1 ∧ commutingCard x = t.2.1 ∧
    (t.2.2 = 0 ∨ commutingCard (x ^ 2) = t.2.2)

/-- The order and centralizer tests are intrinsic automorphism invariants. -/
public theorem orderCentralizerTest_apply (f : MulAut G) (t : ℕ × ℕ × ℕ) (x : G) :
    orderCentralizerTest t (f x) ↔ orderCentralizerTest t x := by
  simp only [orderCentralizerTest, f.orderOf_eq, commutingCard_apply, ← map_pow]
end MulAut
