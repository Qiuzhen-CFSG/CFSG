module
public import Theory.GroupAction.RankThreeBinaryFactorOrbit

/-!
# A two-power number of rank-three binary fixed factors

Keep an elementary binary group A of order eight acting on nontrivial
finite elementary cubic F, and compatible supplied actions of a finite
two-group T on A and F. Whole-A fixed freedom and T-irreducibility make
all active coatom fixed factors one orbit by the preceding theorem.
The orbit-cardinality theorem then makes their number a power of two.

This is the numerical count following Stellmacher (8.6)(21), printed p.45.
Neither transitivity nor the factor count is assumed, and the public
statement retains exactly the original action instances and hypotheses.
-/
open scoped Pointwise

public theorem rank_three_binary_fixed_factor_count_is_two_power
    {A F T : Type*} [Group A] [Finite A] [Group F] [Finite F] [Nontrivial F]
    [Group T] [Finite T] [IsElementaryAbelian 2 A] [IsElementaryAbelian 3 F]
    [MulDistribMulAction T A] [MulDistribMulAction T F] [MulDistribMulAction A F]
    (hA : Nat.card A = 8) (hT : IsPGroup 2 T)
    (hcompat : ∀ (t : T) (a : A) (x : F), t • (a • x) = (t • a) • (t • x))
    (hfull : FixedPoints.subgroup (⊤ : Subgroup A) F = ⊥)
    (hirr : ∀ H : Subgroup F, IsInvariant T F H → H = ⊥ ∨ H = ⊤) :
    ∃ k : ℕ, Nat.card
      {K : Subgroup A // K.index = 2 ∧ FixedPoints.subgroup K F ≠ ⊥} = 2 ^ k := by
  obtain ⟨K,_hKindex,_hKne,hactive⟩ :=
    rank_three_binary_fixed_factors_single_orbit hA hcompat hfull hirr
  obtain ⟨k,hk⟩ := hT.card_orbit K
  exact ⟨k,(Nat.card_congr (Equiv.setCongr hactive)).trans hk⟩
