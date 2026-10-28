module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.PResidual.Defs

/-!
# Inputs to the odd-characteristic Cartan argument

The ambient input retains the actual Sylow subgroup, the intrinsic generalized
Fitting subgroup, and the equality of subgroup products. `CaseThree` records
the algebraic clauses of A.3.15(3) used in the proof of 1.3.4. In particular,
its two factors are intersections with the actual SL₂ subgroup and its actual
centralizer. Its linear and unitary alternatives require group isomorphisms;
the unitary parameter is the fixed-field order, not the matrix-field order.

This is an input interface, not a proof of A.3.15. We retain the concrete
centralizer, cyclicity and divisibility assertions instead of introducing an
unconnected predicate for the source's Cartan terminology. The later argument
is to prove a result from these algebraic clauses, without needing that
additional terminology. In particular, no invariance or canonical choice of
the supplied SL₂ subgroup is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.3.15(3), printed pp. 50–51, and the proof of 1.3.4, pp. 510–511.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan

/-- The signs +1 and -1, also distinguishing the linear and unitary models. -/
inductive Sign where
  | linear
  | unitary
  deriving DecidableEq

/-- The positive integer written `q - δ` in the source. -/
def Sign.torusOrder (δ : Sign) (q : ℕ) : ℕ :=
  match δ with
  | .linear => q - 1
  | .unitary => q + 1

/-- The residue modulo four of the source sign. -/
def Sign.modFour (δ : Sign) : ℕ :=
  match δ with
  | .linear => 1
  | .unitary => 3

/-- Actual projective degree-three models, with the source field convention. -/
def Sign.Model (δ : Sign) (D : Type*) [Group D] (q : ℕ) : Prop :=
  match δ with
  | .linear => ClassicalGroup.IsPSL D 3 q
  | .unitary => ClassicalGroup.IsPSU D 3 q

variable {J : Type*} [Group J]

/-- The genuine ambient hypotheses in the prime-subgroup case of A.3.15.
The three-residual condition is `O³(B) ≠ 1`, not a condition on the three-core. -/
structure AmbientInput (κ : GroupClass) (D B : Subgroup J) (S : Sylow 2 J)
    (p : ℕ) : Prop where
  sqtk : IsSQTK κ J
  fitting : generalizedFitting J = D
  simple : IsSimpleGroup D
  prime : p.Prime
  odd : Odd p
  large : 3 < p
  p_group : IsPGroup p B
  inside : B ≤ D
  permutes : (B : Set J) * (S : Set J) = (S : Set J) * (B : Set J)
  three_residual : pResidual 3 B ≠ ⊥

/-- The cyclic centralizer factorization. The two factors commute, so the
join here is also their setwise product. This definition asserts no invariance. -/
structure CyclicDecomposition (B K : Subgroup J) : Prop where
  left_cyclic : IsCyclic (B ⊓ K : Subgroup J)
  right_cyclic : IsCyclic (B ⊓ centralizer (K : Set J) : Subgroup J)
  generated : (B ⊓ K) ⊔ (B ⊓ centralizer (K : Set J)) = B

/-- The concrete algebraic data supplied by A.3.15(3). The characteristic
`q` is prime; `p` in `AmbientInput` is the prime called `r` in that lemma.
Inversion is by an actual element of `S ∩ K`. -/
structure CaseThree (D B S K : Subgroup J) (q : ℕ) [Fact q.Prime]
    (δ ε : Sign) : Prop extends CyclicDecomposition B K where
  odd_characteristic : Odd q
  model : δ.Model D q
  sl2 : Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod q))
  sl2_inside : K ≤ D
  centralizer_dvd : Nat.card (B ⊓ centralizer (K : Set J) : Subgroup J) ∣ δ.torusOrder q
  sl2_dvd : Nat.card (B ⊓ K : Subgroup J) ∣ ε.torusOrder q
  sylow_sign : q % 4 = ε.modFour
  inverted : ∃ t ∈ S ⊓ K, ∀ b ∈ B ⊓ K, t * b * t⁻¹ = b⁻¹

/-- Normality follows from the intrinsic generalized-Fitting equality. -/
theorem AmbientInput.normal [Finite J] {κ : GroupClass} {D B : Subgroup J}
    {S : Sylow 2 J} {p : ℕ} (h : AmbientInput κ D B S p) : D.Normal := by
  rw [← h.fitting]
  infer_instance

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
