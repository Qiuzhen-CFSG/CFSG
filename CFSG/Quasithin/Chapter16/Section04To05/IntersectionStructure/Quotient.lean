module

public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.Local
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# The fixed quotient H* and ambient prime-to-p residuals

The star in §§16.4–16.5 always means the image in H/K, where H = N_G(L)
and K = C_G(L). In particular C_G(i)* is its image in this fixed quotient;
it is not a new quotient by an arbitrarily chosen prime-to-p core.

`primeToResidualIn` embeds O^{p'}(A) in the ambient group. This is distinct
from both the prime-to-p core O_{p'}(A) and the p-residual O^p(A).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Notation
16.4.1 and Lemma 16.4.5, pp.1183–1184. The residual alternatives themselves
require the A.3.18 application and the (E2) model exclusions.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup
variable {G : Type*} [Group G]

/-- The fixed action quotient H/K, with K normal relative to H. -/
abbrev componentActionQuotient (L : Subgroup G) :=
  normalizer (L : Set G) ⧸
    (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))

/-- The quotient map with the source's fixed kernel K. -/
abbrev componentActionQuotientMap (L : Subgroup G) :
    normalizer (L : Set G) →* componentActionQuotient L :=
  QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))

/-- The image A* in H/K. The explicit containment prevents silently replacing
A by A ∩ H when applying the source notation. -/
def starImage (L A : Subgroup G) (_hA : A ≤ normalizer (L : Set G)) :
    Subgroup (componentActionQuotient L) :=
  (A.subgroupOf (normalizer (L : Set G))).map (componentActionQuotientMap L)

/-- O^{p'}(A), retained as an actual subgroup of the ambient group. -/
def primeToResidualIn (p : ℕ) (A : Subgroup G) : Subgroup G :=
  (primeToResidual p A).map A.subtype

end CFSG.Quasithin.Chapter16.Intersections
