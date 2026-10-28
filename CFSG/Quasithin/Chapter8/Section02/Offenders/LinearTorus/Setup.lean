module

public import Theory.Representation.HermitianTensorThree.ParabolicTorus.Contracts

/-!
# The marked linear-three torus configuration in 8.2.3

In the source branch `k > 1`, the overgroup acts on the actual descended Hermitian tensor space, its
solvable residual is the actual SL₃ image, and the cyclic actor normalizes
the specified elementary abelian subgroup. The central intersection is
retained as a subspace `Z`, with the E.2.14(9) identification `Z = C_V(x)`
and its inclusion in `C_V(A)`.

The numerical inputs are earlier source conclusions, not conclusions of the
torus argument: the 8.2.2(7) rank identity, the E.2.14(3) natural-module
degree in the linear case (or odd parameter in the Suzuki case), and the
H.4.2/H.4.4(3) rank and fixed-codimension bounds. The enclosing 8.2.2–5
assembly owns their derivation and the original-module identification.

The two lemmas extract the inequalities used to exclude a nontrivial
coefficient action and the intermediate nonsplit parabolic case.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.226–227, 380–381, and 715–716.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter8.Section02.Offenders.LinearThreeTorus
open Representation.HermitianTensorThree
open Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open Representation.BinaryOffender

variable (n k : ℕ) [NeZero n]

/-- The literal model and the precise preceding source inputs used below.
No split-torus containment or exponent divisibility is included. -/
structure Setup where
  M : Subgroup (BinaryAut n)
  source : SourceOvergroup n M
  A : Subgroup M
  elementary : IsElementaryAbelian 2 A
  x : M
  order : orderOf x = 2 ^ k - 1
  normalizes : x ∈ Subgroup.normalizer (A : Set M)
  parabolic : PreservesMaximalParabolic n x.val
  Z : Submodule (ZMod 2) (Space n)
  fixed_eq : Z = fixedSpace (overgroupAction n M) (Subgroup.zpowers x)
  fixed_le_actor : Z ≤ fixedSpace (overgroupAction n M) A
  rank_identity : Module.finrank (ZMod 2) Z + k + rank A = 9 * n
  module_degree : k ∣ rank A ∨ Odd k
  actor_rank_le : rank A ≤ 4 * n
  actor_fixedCodim_ge : 5 * n ≤ fixedCodim (overgroupAction n M) A

namespace Setup
variable {n k}

/-- Strictly below the endpoint, E.2.14(9)'s fixed space exceeds one third of V. -/
theorem fixed_rank_gt_three_mul (s : Setup n k) (hk : k < 2 * n) :
    3 * n < Module.finrank (ZMod 2) s.Z := by
  have := s.rank_identity
  have := s.actor_rank_le
  omega

/-- H.4.4(3) applies to the original actor; the E.2.14 fixed-space inclusion
transfers its lower bound to the cyclic actor's codimension. -/
theorem five_mul_le_rank_sum (s : Setup n k) : 5 * n ≤ k + rank s.A := by
  have hdim := finrank_binary n
  have hfixed := fixedCodim_add_finrank (overgroupAction n s.M) s.A
  have hle := Submodule.finrank_mono s.fixed_le_actor
  have hr := s.rank_identity
  have hbound := s.actor_fixedCodim_ge
  omega

end Setup
end CFSG.Quasithin.Chapter8.Section02.Offenders.LinearThreeTorus
