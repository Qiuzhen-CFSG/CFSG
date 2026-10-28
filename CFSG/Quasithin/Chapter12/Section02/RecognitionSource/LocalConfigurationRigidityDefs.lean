module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationDefs

/-!
# Shared centralizer conclusions before the two branches of 12.2.25

Write I=PUV, R=C_T(U), and Y=O²(N_L(U∩V)). The opening part of the
source proof splits the two relevant centralizers, kills their common
central factor, and proves that R is elementary with |C_T(L)|≤2. The
Thompson calculation also shows that Y normalizes R.

These are intermediate conclusions to be constructed from the original
source hypotheses. The record does not assert their existence, the vanishing
of C_T(L), self-normalization of L, a dimension cutoff, or any complement.
The dimension-three transfer argument and the higher-dimensional component
argument may consume this same boundary independently.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
12.2.25, printed pp.804--806, through the displayed Y≤N_G(R) on p.805.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G]

/-- The actual two-residual of the hyperplane normalizer in L, embedded in G. -/
def rigidityHyperplaneResidual (L U V : Subgroup G) : Subgroup G :=
  (pResidual 2 ↥(L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G))).map
    (L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)).subtype

/-- The common source calculation, before assuming either d=3 or d>3. -/
structure LocalRigidityCentralizers (T : Sylow 2 G) (L V U P : Subgroup G) : Prop where
  kernel_split : (T : Subgroup G) ⊓ centralizer (V : Set G) =
    V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))
  kernel_disjoint : Disjoint V ((T : Subgroup G) ⊓ centralizer (L : Set G))
  centralizer_split : (T : Subgroup G) ⊓ centralizer (U : Set G) =
    U ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))
  centralizer_disjoint : Disjoint U ((T : Subgroup G) ⊓ centralizer (L : Set G))
  common_trivial : ((T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
    ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) = ⊥
  elementary : IsElementaryAbelian 2 ↥((T : Subgroup G) ⊓ centralizer (U : Set G))
  component_centralizer_card : Nat.card ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) ≤ 2
  sylow_split : (T : Subgroup G) = ((T : Subgroup G) ⊓ L) ⊔
    ((T : Subgroup G) ⊓ centralizer (L : Set G))
  sylow_disjoint : Disjoint ((T : Subgroup G) ⊓ L)
    ((T : Subgroup G) ⊓ centralizer (L : Set G))
  component_centralizer_central : (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
    centralizer (T : Set G)
  pair_centralizer_central : (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G) ≤
    centralizer (T : Set G)
  hyperplane_centralizer : (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) =
    U ⊔ V ⊔ ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G))
  residual_normalizes : rigidityHyperplaneResidual L U V ≤
    normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
