module
public import Mathlib.FieldTheory.Fixed
public import Mathlib.Algebra.Ring.Action.Subobjects
public import Theory.SpecificGroups.GL2.Semilinear
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.GL2.OddExtensionIndex

/-!
# Sylow subgroups fixed by odd coefficient automorphisms

Let F be a finite field of odd cardinality and A an odd-order subgroup of
its actual field automorphism group. Every valid determinant two-power
level in GL₂(F) has a Sylow two subgroup fixed pointwise by A under the
coefficient action. This supplies the linear-model fixed-Sylow step in
ABG II.3, Proposition 3(iv), article pp. 27–28, including the small fields.

Use the canonical action restricted to A and its actual fixed subfield K.
Artin's fixed-field theorem gives [F:K]=|A|. Hence K has odd cardinality and
the coefficient embedding GL₂(K) → GL₂(F) has odd index. The image of a
Sylow subgroup of this range is therefore Sylow in GL₂(F), proving the
full-group theorem used for the projective quotient. Intersecting
with the normal determinant level gives a Sylow of that level; its entries
belong to K, so every element of A fixes it pointwise. The intersection
argument works for any level; the public theorem retains the source's
valid-level divisibility hypothesis.
-/

namespace Matrix.GeneralLinearGroup

/-- An odd subgroup of actual coefficient automorphisms fixes some GL2 Sylow two-subgroup. -/
public theorem exists_gl_sylow_fixed_by_odd_coefficient_subgroup
    (F : Type*) [Field F] [Finite F] (hF : Odd (Nat.card F))
    (A : Subgroup (F ≃+* F)) (hA : Odd (Nat.card A)) :
    ∃ Q : Sylow 2 (GL (Fin 2) F),
      ∀ (σ : A) (x : Q), coefficientEquiv σ.val x.val = x.val := by
  classical
  let : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) DFunLike.coe_injective
  let := Fintype.ofFinite A
  let : FaithfulSMul A F := ⟨fun h => Subtype.ext (RingEquiv.ext h)⟩
  let K := FixedPoints.subfield A F
  have hr : Odd (Module.finrank K F) := by
    simpa only [K, FixedPoints.finrank_eq_card, Nat.card_eq_fintype_card] using hA
  have hK : Odd (Nat.card K) := by
    apply Nat.not_even_iff_odd.mp
    intro hk
    apply (Nat.not_even_iff_odd.mpr hF)
    rw [Module.natCard_eq_pow_finrank (K := K) (V := F)]
    exact Nat.even_pow.mpr ⟨hk, (Module.finrank_pos (R := K) (M := F)).ne'⟩
  let C := (map (n := Fin 2) (algebraMap K F)).range
  have hC : ¬ 2 ∣ C.index := (odd_index_map_of_odd_finrank K F hK hr).not_two_dvd_nat
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := C)
  let Q : Sylow 2 (GL (Fin 2) F) :=
    (P.isPGroup'.map C.subtype).toSylow (by
      rw [Subgroup.index_map_subtype]
      exact Nat.Prime.not_dvd_mul Nat.prime_two P.not_dvd_index hC)
  refine ⟨Q, ?_⟩
  intro σ x
  have hx : x.val ∈ C := by
    obtain ⟨y, _, hy⟩ := x.property
    exact hy ▸ y.property
  obtain ⟨y, hy⟩ := hx
  rw [← hy]
  ext i j
  exact (y i j).property σ

/-- An odd subgroup of coefficient automorphisms fixes some actual Sylow two
subgroup of a valid determinant two-power level pointwise. -/
public theorem exists_sylow_fixed_by_odd_coefficient_subgroup
    (F : Type*) [Field F] [Finite F] (hF : Odd (Nat.card F))
    (A : Subgroup (F ≃+* F)) (hA : Odd (Nat.card A)) (m : ℕ)
    (_hm : 2 ^ m ∣ Nat.card F - 1) :
    ∃ S : Sylow 2 (determinantTwoPower F m),
      ∀ (σ : A) (x : S), coefficientEquiv σ.val x.val.val = x.val.val := by
  obtain ⟨Q, hQ⟩ := exists_gl_sylow_fixed_by_odd_coefficient_subgroup F hF A hA
  obtain ⟨S, hS⟩ := Q.exists_subgroupOf_eq_of_normal (determinantTwoPower F m)
  refine ⟨S, ?_⟩
  intro σ x
  have hxQ : x.val.val ∈ Q := by
    have hxS : x.val ∈ (S : Subgroup (determinantTwoPower F m)) := x.property
    rw [hS] at hxS
    exact hxS
  exact hQ σ ⟨x.val.val, hxQ⟩

end Matrix.GeneralLinearGroup
