module

public import Theory.Representation.BinaryOffender.IrreducibleOrbitGeometry
public import Theory.LinearAlgebra.BinaryPartialSpread

/-!
# B.7.2(1): the regular-orbit contradiction

After the moved-space and stabilizer reductions, let V = I + Iᵃ and
N_A(I) = 1. The actual orbit of I has size |A|. Its images in V/C_V(X)
are pairwise disjoint and have common positive dimension n; the quotient
has dimension 2n. The a-diagonal also has dimension n, is fixed by A,
and is disjoint from every orbit image. Counting their nonzero vectors
and using n ≤ codim C_V(A) ≤ rank A forces |A| = 2^n and gives a partition
of the nonzero quotient vectors.

Each orbit image is X-invariant, so the complementary diagonal is invariant.
The contradiction is proved inside the quotient: [X,A] = X makes the
A-fixed diagonal X-fixed, and disjointness then puts [I,X] = I inside C_V(X).
No lifting of quotient invariance to invariance in V is used.

The final theorem retains faithfulness as part of the requested reduced
contract; the supplied trivial stabilizer has already used it. The parent
B.7.2 theorem must supply the moved-space reduction and trivial stabilizer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.7.2(1), printed p. 119 (PDF p. 130).
-/

public section

namespace CFSG.Quasithin.ChapterB
open Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Counting the regular orbit together with the diagonal gives equality in
both the packing bound and the offender lower bound. -/
theorem quotientOrbit_cover_and_card [Finite G] [FiniteDimensional (ZMod 2) V]
    {X A : Subgroup G} {I : Submodule (ZMod 2) V} {a : G}
    (hA : IsBestOffender ρ A) (haA : a ∈ A)
    (hI : IsIrrPlus ρ X I) (hIa : IsIrrPlus ρ X (I.map (ρ a)))
    (hne : I ≠ I.map (ρ a)) (hXA : ⁅X, A⁆ = X)
    (ha : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v)
    (hsup : I ⊔ I.map (ρ a) = ⊤) (hstab : A ⊓ subspaceStabilizer ρ I = ⊥) :
    Nat.card A = 2 ^ Module.finrank (ZMod 2) (I.map (fixedSpace ρ X).mkQ) ∧
    ∀ q : V ⧸ fixedSpace ρ X, q ≠ 0 →
      q ∈ (diagonalSubspace ρ I a).map (fixedSpace ρ X).mkQ ∨
        ∃ b : A, q ∈ (I.map (ρ b)).map (fixedSpace ρ X).mkQ := by
  let n := Module.finrank (ZMod 2) (I.map (fixedSpace ρ X).mkQ)
  let U : Option A → Submodule (ZMod 2) (V ⧸ fixedSpace ρ X) := fun i =>
    match i with
    | none => (diagonalSubspace ρ I a).map (fixedSpace ρ X).mkQ
    | some b => (I.map (ρ b)).map (fixedSpace ρ X).mkQ
  have hAN : A ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hXA.le
  have hn : 0 < n := hI.finrank_quotientImage_pos ρ
  have hdimQ : Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ X) = 2 * n :=
    finrank_quotient_eq_double ρ hI hIa hne (hAN haA) hsup
  have hdimD := finrank_quotientDiagonal_eq ρ hI hIa hne (hAN haA)
  have hdim : ∀ i, Module.finrank (ZMod 2) (U i) = n := by
    intro i
    cases i with
    | none => exact hdimD
    | some b => exact finrank_quotientOrbit ρ X I (hAN b.property)
  have hdis : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some b => exact quotientDiagonal_disjoint_orbit ρ haA hI hIa hne hXA ha b
    | some b =>
      cases j with
      | none => exact (quotientDiagonal_disjoint_orbit ρ haA hI hIa hne hXA ha b).symm
      | some c =>
        exact quotientOrbit_pairwise_disjoint ρ hI hAN hstab
          (fun h => hij (congrArg some h))
  have hncode : n ≤ fixedCodim ρ A := by
    change Module.finrank (ZMod 2) (I.map (fixedSpace ρ X).mkQ) ≤ _
    rw [← hdimD]
    exact finrank_quotientDiagonal_le_fixedCodim ρ X A I haA
  have hlower : 2 ^ n ≤ Nat.card A := hA.two_pow_le_card_of_le_fixedCodim ρ hncode
  have hp : 1 < 2 ^ n := by
    have := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) hn
    omega
  have hfactor : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [Nat.mul_comm 2 n, pow_mul]
    have := Nat.sub_add_cancel (show 1 ≤ 2 ^ n by omega)
    have hp2 : 1 ≤ (2 ^ n) ^ 2 := one_le_pow₀ (by omega)
    have hp2sub := Nat.sub_add_cancel hp2
    nlinarith only [this, hp2sub]
  have hcardOption : Nat.card (Option A) = Nat.card A + 1 := by
    let := Fintype.ofFinite A
    simp only [Nat.card_eq_fintype_card, Fintype.card_option]
  have hbound := Submodule.binary_partialSpread_bound U hdis hdim
  rw [hcardOption, hdimQ, hfactor] at hbound
  have hupper : Nat.card A ≤ 2 ^ n := by
    have hpos : 0 < 2 ^ n - 1 := by omega
    have := Nat.le_of_mul_le_mul_right hbound hpos
    omega
  have heq : Nat.card A = 2 ^ n := Nat.le_antisymm hupper hlower
  refine ⟨heq, ?_⟩
  have heqpack : Nat.card (Option A) * (2 ^ n - 1) =
      2 ^ Module.finrank (ZMod 2) (V ⧸ fixedSpace ρ X) - 1 := by
    rw [hcardOption, heq, hdimQ, hfactor]
  intro q hq
  obtain ⟨i, hi⟩ := Submodule.binary_partialSpread_cover U hdis hdim heqpack q hq
  cases i with
  | none => exact Or.inl hi
  | some b => exact Or.inr ⟨b, hi⟩

/-- The reduced regular-orbit contradiction in B.7.2(1). -/
theorem irreducible_orbit_contradiction [Finite G] [FiniteDimensional (ZMod 2) V]
    (_hfaithful : Function.Injective ρ) {X A : Subgroup G}
    {I : Submodule (ZMod 2) V} {a : G}
    (hA : IsBestOffender ρ A) (hXA : ⁅X, A⁆ = X) (haA : a ∈ A)
    (ha : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v)
    (hI : IsIrrPlus ρ X I) (hIa : IsIrrPlus ρ X (I.map (ρ a)))
    (hne : I ≠ I.map (ρ a)) (hsup : I ⊔ I.map (ρ a) = ⊤)
    (hstab : A ⊓ subspaceStabilizer ρ I = ⊥) : False := by
  exact irreducibleOrbit_contradiction_of_cover ρ haA hI hIa hne hXA ha
    (quotientOrbit_cover_and_card ρ hA haA hI hIa hne hXA ha hsup hstab).2
end CFSG.Quasithin.ChapterB
