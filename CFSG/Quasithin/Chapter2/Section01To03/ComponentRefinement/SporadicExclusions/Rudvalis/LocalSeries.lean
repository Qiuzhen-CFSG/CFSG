module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Rudvalis.Reduction

/-!
# Local-series contracts for the Rudvalis block calculation

Source: Aschbacher–Smith, 2.3.9(7), printed p.526; GLS, volume 3,
Table 5.3r, printed p.279, and its justification on printed pp.291–292.

The candidate local groups have shapes 2^(3+8).L₃(2) and E₆₄.G₂(2).
Their nonabelian simple factors have orders 168 and 6048 respectively;
the full group G₂(2) and its derived subgroup are distinct. A series with
these factors and two-group factors accommodates central two-kernels and
permutations of component conjugates by the supplied Sylow subgroup.

`LocalFactorSeries` specifies a finite series of actual subgroups, with
normality relative to the next term and conditions on its actual quotients.
The numerical conditions are only for exclusion; they do not identify any
factor with a named group. Constructing such series for the actual local
overgroups is an outstanding part of the model calculation.

`LocalGeometry` separates that construction from the general analysis of
short subnormal blocks in groups with these series. Its generator conditions
use the canonical map to the concrete Rudvalis model. The final conditional
constructor uses the proved central-kernel transfer from `Reduction`.
Neither required input is proved here, so no Rudvalis block cover or source
exclusion is asserted.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase

open Subgroup ChapterC Theory.GroupTheory

variable {G : Type*} [Group G]

/-- A finite relative normal series with two-group factors and simple factors
of the two orders needed by the proposed Rudvalis local calculation. -/
structure LocalFactorSeries (K : Type*) [Group K] where
  length : ℕ
  term : Fin (length + 1) → Subgroup K
  first : term 0 = ⊥
  last : term (Fin.last length) = ⊤
  ascending : ∀ i : Fin length, term i.castSucc ≤ term i.succ
  normal : ∀ i : Fin length, ((term i.castSucc).subgroupOf (term i.succ)).Normal
  factor : ∀ i : Fin length, letI := normal i
    let F := term i.succ ⧸ (term i.castSucc).subgroupOf (term i.succ)
    IsPGroup 2 F ∨ (IsSimpleGroup F ∧ (Nat.card F = 168 ∨ Nat.card F = 6048))

/-- Contract for constructing the actual local overgroups. It includes
nontrivial self-centralizing cores, the supplied S, and the concrete generator
tests. It contains no block-exclusion premise. -/
structure LocalGeometry (L S : Subgroup G) {z : G}
    (d : SporadicQuotientInput L z .ru) where
  locals : Set (Subgroup G)
  within : ∀ K ∈ locals, K ≤ L ⊔ S
  even : ∀ K ∈ locals, K ∈ CFSG.Quasithin.Chapter1.HeOver G (S : Set G)
  series : ∀ K ∈ locals, Nonempty (LocalFactorSeries K)
  a_mem : Rudvalis.a ∈ ((sSup locals).subgroupOf L).map (quotientMap d)
  b_mem : Rudvalis.b ∈ ((sSup locals).subgroupOf L).map (quotientMap d)

/-- Conditional assembly from an actual local geometry and a separately proved
subnormal-block theorem for its factor series. Both inputs remain obligations. -/
def LocalGeometry.toCentralizerBlockCover {H L M : Subgroup G}
    {S : Sylow 2 H} {z : G} (h : LocalSetup H L M S z)
    {d : SporadicQuotientInput L z .ru}
    (c : LocalGeometry L ((S : Subgroup H).map H.subtype) d)
    (hseries : ∀ K : Subgroup G, Nonempty (LocalFactorSeries K) →
      ∀ B : Subgroup K, IsChiZeroBlockIn B → False) :
    CentralizerBlockCover L M ((S : Subgroup H).map H.subtype) z where
  locals := c.locals
  generated := le_centralizer_sup_of_generators h d c.a_mem c.b_mem
  within := c.within
  even := c.even
  obstruction := by
    intro K hK B hb _
    exact (hseries K (c.series K hK) B hb).elim

end CFSG.Quasithin.Chapter2.ComponentRefinement.RudvalisCase

end
