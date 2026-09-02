module

public import Mathlib.GroupTheory.Sylow
public import Theory.PrimeRank

/-!
# Quasithin finite groups

Let `G` be a finite group.  A 2-local subgroup of `G` is the normalizer of a
nontrivial 2-subgroup.  Write `calM G` for the maximal such subgroups.  For a
prime `p`, `pRank p H` is the largest rank of an elementary abelian `p`-subgroup
of `H`, and `e G` is the largest `p`-rank of a member of `calM G`, as `p` ranges
over the odd primes.  The group is quasithin when `e G ≤ 2`.

A Sylow 2-subgroup `T : Sylow 2 G` is commonly fixed while using these
definitions, but none of the invariants depends on the choice of `T`.
-/


/-- A subgroup is *2-local* when it is the normalizer of a nontrivial
2-subgroup. -/
public def IsTwoLocal {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  ∃ Q : Subgroup G, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ M = Subgroup.normalizer (Q : Set G)

/-- A 2-local subgroup maximal among the 2-local subgroups under inclusion. -/
public def IsMaximalTwoLocal {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  Maximal (IsTwoLocal (G := G)) M

/-- The set `𝒨` of maximal 2-local subgroups of `G`. -/
public def calM (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | IsMaximalTwoLocal M}

/-- The quasithin invariant `e(G)`: the maximum odd-prime rank among the
maximal 2-local subgroups of `G`. -/
public noncomputable def e (G : Type*) [Group G] [Finite G] : ℕ :=
  sSup
    {n : ℕ | ∃ M : Subgroup G, M ∈ calM G ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧ n ≤ primeRank p M}

/-- A finite group is *quasithin* when its invariant `e(G)` is at most two. -/
public def IsQuasithin (G : Type*) [Group G] [Finite G] : Prop := e G ≤ 2

