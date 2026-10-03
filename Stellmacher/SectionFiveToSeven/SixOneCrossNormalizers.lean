module

public import Stellmacher.SectionFiveToSeven.FiveFourSharedOmega
public import Stellmacher.SectionFiveToSeven.PFamilyBridge
public import Stellmacher.SectionThree.ThreeNineBaumannNormalizers
public import Stellmacher.BaumannTwoOvergroupTransport
public import Stellmacher.SectionFiveToSeven.SixThreeCrossNormalizers

/-!
# Cross-normalizers for the global Sylow branch of (6.1)

Under Hypothesis 2 with `S=S₀`, local-family members `E` and `F` sharing
`B(S)` normalize the opposite omega-residual commutators whenever their
actual join has nontrivial 2-core. This preserves the exact (6.1) interface
as a specialization of the cross-normalizer theorem for both (5.4) branches.

The generalized theorem supplies the shared omega containment, local
solvability, Thompson transport, and residual-Sylow generation argument.
Here `S=S₀` establishes its first alternative. The actual join and the
supplied maximal local subgroup are retained.

Source: Stellmacher (6.1), Journal of Algebra 190 (1997), p.30, its
applications of (5.4) and (3.9), in `refs/latex/stellmacher-n-group.tex`.
The earlier public imports remain available to existing consumers.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

public theorem sixOne_cross_normalizers
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) (hS : S = (S0 : Subgroup H))
    (E F M : Subgroup H)
    (hE : E ∈ PFamily (⊤ : Subgroup H) (baumannIn S))
    (hF : F ∈ PFamily (⊤ : Subgroup H) (baumannIn S))
    (hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (hcore : twoCoreIn (E ⊔ F) ≠ ⊥) :
    F ≤ Subgroup.normalizer
      ((⁅omegaOneCenter (baumannIn S), twoResidualIn E⁆ : Subgroup H) : Set H) ∧
    E ≤ Subgroup.normalizer
      ((⁅omegaOneCenter (baumannIn S), twoResidualIn F⁆ : Subgroup H) : Set H) := by
  exact sixThree_cross_normalizers S0 S P1 P2 h E F M hE hF hM hcore (Or.inl hS)

end Stellmacher.SectionsFiveToSeven
