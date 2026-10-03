module

public import Theory.GroupAction.Invariant
public import Theory.GroupTheory.Hall.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# Fixed points in an invariant Hall product

ABG II.8 Lemma8 (article p65, PDF66) states that if a finite two-group
acts on an odd-order group K=XY, with invariant subgroups X,Y and X Hall,
then C_K(S)=C_X(S)C_Y(S) as an ordered set product.

The source selects an invariant Hall complement in Y and uses uniqueness
of its factorization with X. Here an elementary orbit-counting argument
avoids odd-order solvability: the factorizations of each fixed element
form an S-set in bijection with X∩Y. Its cardinality is odd, so the
two-group fixed-point theorem supplies a fixed factorization. The generic
fixed-factor theorem records exactly the needed oddness of X∩Y; it does not
require K itself to have odd order or a Hall hypothesis. The original Hall
factorization theorem retains its public interface and follows from this
stronger local statement. The generic theorem also supplies the normalized
prime-subgroup step in KS11.1.8 signalizer transitivity. All fixed-point
subgroups are computed with the given ambient action.
-/

open scoped Pointwise

private def factorFiberEquiv {K : Type*} [Group K]
    (X Y : Subgroup K) (x y : K) (hx : x ∈ X) (hy : y ∈ Y) :
    ↥(X ⊓ Y) ≃ {z : K // z ∈ X ∧ z⁻¹ * (x * y) ∈ Y} where
  toFun element := ⟨x * element, X.mul_mem hx element.property.1, by
    simpa [mul_assoc] using Y.mul_mem (Y.inv_mem element.property.2) hy⟩
  invFun element := ⟨x⁻¹ * element, X.mul_mem (X.inv_mem hx) element.property.1, by
    simpa [mul_inv_rev, mul_assoc] using
      Y.mul_mem hy (Y.inv_mem element.property.2)⟩
  left_inv element := by ext; simp
  right_inv element := by ext; simp

/-- A fixed element in an invariant subgroup product has fixed factors if
the subgroup intersection has odd order. -/
public theorem fixed_mem_mul_of_odd_inf {S K : Type*} [Group S] [Group K]
    [Finite K] [MulDistribMulAction S K]
    (hS : IsPGroup 2 S) (X Y : Subgroup K)
    [hX : IsInvariant S K X] [hY : IsInvariant S K Y]
    (hodd : Odd (Nat.card (X ⊓ Y : Subgroup K)))
    {c : K} (hc : c ∈ fixedPointSubgroup S K)
    (hcXY : c ∈ (X : Set K) * (Y : Set K)) :
    c ∈ ((X ⊓ fixedPointSubgroup S K : Subgroup K) : Set K) *
      ((Y ⊓ fixedPointSubgroup S K : Subgroup K) : Set K) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hcXY
  let Fiber := {z : K // z ∈ X ∧ z⁻¹ * c ∈ Y}
  have hfiber : Odd (Nat.card Fiber) := by
    have hcard : Nat.card Fiber = Nat.card ↥(X ⊓ Y) := by
      subst c
      exact (Nat.card_congr (factorFiberEquiv X Y x y hx hy)).symm
    rw [hcard]
    exact hodd
  let : MulAction S Fiber :=
    { smul := fun actor element => ⟨actor • element.val,
        (hX.invariant actor element.val).mp element.property.1, by
          have hmem := (hY.invariant actor (element.val⁻¹ * c)).mp element.property.2
          simpa only [smul_mul', smul_inv', hc actor] using hmem⟩
      one_smul := fun element => Subtype.ext (one_smul S element.val)
      mul_smul := fun actor other element =>
        Subtype.ext (mul_smul actor other element.val) }
  have hnotdvd : ¬2 ∣ Nat.card Fiber := by
    simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using hfiber
  obtain ⟨element, hfixed⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card Fiber hnotdvd
  have helement : ∀ actor : S, actor • element.val = element.val := by
    intro actor
    exact congrArg Subtype.val (hfixed actor)
  refine Set.mem_mul.mpr ⟨element.val, ⟨element.property.1, helement⟩,
    element.val⁻¹ * c, ⟨element.property.2, ?_⟩, by simp⟩
  intro actor
  simp only [smul_mul', smul_inv', helement actor, hc actor]

public theorem fixedPoints_mul_of_hall_factorization
    {S K : Type*} [Group S] [Finite S] [Group K] [Finite K]
    [MulDistribMulAction S K] (hS : IsPGroup 2 S) (hK : Odd (Nat.card K))
    (X Y : Subgroup K) [IsInvariant S K X] [IsInvariant S K Y]
    {π : Set Nat.Primes} (_hHall : IsHallSubgroup π X)
    (hXY : (X : Set K) * (Y : Set K) = Set.univ) :
    (fixedPointSubgroup S K : Set K) =
      ((X ⊓ fixedPointSubgroup S K : Subgroup K) : Set K) *
        ((Y ⊓ fixedPointSubgroup S K : Subgroup K) : Set K) := by
  apply Set.Subset.antisymm
  · intro c hc
    exact fixed_mem_mul_of_odd_inf hS X Y
      (hK.of_dvd_nat (Subgroup.card_subgroup_dvd_card (X ⊓ Y))) hc (by rw [hXY]; trivial)
  · intro c hc
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hc
    exact (fixedPointSubgroup S K).mul_mem hx.2 hy.2
