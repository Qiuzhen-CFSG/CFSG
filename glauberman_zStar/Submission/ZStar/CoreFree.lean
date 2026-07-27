import Mathlib
import Submission.FeitThompson.FinalTheorem
import Submission.ZStar.BlockArgument
import Submission.ZStar.CoreFreeAssembly
import Submission.ZStar.MinimalSteps
import Submission.ZStar.OddCommutators
import Submission.ZStar.PrincipalBlockFactory

/-!
# The core-free Z*-theorem

When `O_{2'}(G) = 1`, a weakly closed involution that is central in a Sylow
2-subgroup must be central in G.

The required principal-`2`-block data is constructed uniformly and fed into
the strong-induction assembly in `CoreFreeAssembly.lean`.
-/

namespace Submission.ZStar

open Subgroup

/-- **Glauberman's Z*-theorem, core-free case.**

If the odd core is trivial, then a weakly closed involution that is central in
a Sylow 2-subgroup lies in the center of G.

**Proof outline** (Glauberman, J. Algebra 4 (1966)):
1. Let `Ω` be the conjugacy class of `t`.  The permutation character `π` of the
   `G`-action on `Ω` satisfies `π(1) = |Ω|` and `π(t) = 1` (t fixes only itself).
2. For any irreducible character `χ` of `G`, the scalar product `[π, χ]` is
   `(χ(t) * χ(1)) / |C_G(t)|` plus a 2-regular contribution.
3. If `χ` belongs to the principal 2-block `B₀(G)`, then `χ(t)/χ(1)` is a
   2-adic unit and certain congruences force `χ(t) ≠ 0`.
4. Under `O_{2'}(G) = 1`, every faithful irreducible character lies in the
   principal 2-block.  The block constraints imply `t` acts trivially in every
   irreducible representation, hence `t ∈ Z(G)`.

The formal proof below packages those block-theoretic ingredients through the
unconditional factory in `PrincipalBlockFactory.lean`.
-/
theorem glauberman_zstar_corefree
    {G : Type*} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥)
    (S : Sylow 2 G) (t : G)
    (htI : IsInvolution t)
    (htS : t ∈ (S : Subgroup G))
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G)) :
    t ∈ Subgroup.center G := by
  exact glauberman_zstar_corefree_of_exists_principalTwoBlockData
    PrincipalBlockFactory.principalTwoBlockData_factory
    hcore S t htI htS htCentral htWeak

end Submission.ZStar
