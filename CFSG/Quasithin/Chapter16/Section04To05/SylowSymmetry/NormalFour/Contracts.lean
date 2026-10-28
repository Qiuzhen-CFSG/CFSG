module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.NormalFour.Elementary
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The remaining normal-four and TI interface

`CoverInput` records the intrinsic cover facts consumed in the order argument:
the center is a two-group, and a nonsplit involution lift puts every
2-subgroup of the actual outer automorphism group at order at most two.
The latter follows in the source from 16.1.2 and I.2.2(3b), excluding `L₃(4)`
and inspecting the remaining nonsimple covers. It is an explicit model
obligation, not a theorem supplied by this module.

`SaturatedProjection` describes the outcome of the elementary-image and
order arguments. Its constructor is proved separately from these definitions.
It preserves the actual projection and the relative normality of `S` in `C`.
It asserts neither the normal-four construction nor terminal centrality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 16.4.10, printed p.1193.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.NormalFour
open Subgroup
variable {G : Type*} [Group G]

/-- The precise intrinsic consequences of the cover catalogue needed by
this reduction. The source-theorem owner must prove these for its actual `L`. -/
structure CoverInput (L : Subgroup G) : Prop where
  center_two : IsPGroup 2 (center L)
  outer_bound_of_nonsplit : (∃ l : L, l ^ 2 ∈ center L ∧ l ^ 2 ≠ 1) →
    ∀ Q : Subgroup (MulAut.Outer L), IsPGroup 2 Q → Nat.card Q ≤ 2

/-- Data produced before constructing the normal subgroup of order four. -/
structure SaturatedProjection (C L A S : Subgroup G) where
  configuration : ProjectionConfiguration C L A S
  projection : letI := configuration.overlap_normal; Projection S L A
  two_group : IsPGroup 2 C
  abelian : IsMulCommutative S
  normal_inside : (S.subgroupOf C).Normal
  kernel_card : Nat.card (L.subgroupOf S) = 2
  card_eq : Nat.card S = 2 * Nat.card A
  full_image : letI := configuration.overlap_normal; projection.inverseImage ⊤ = ⊤

/-- The actual direct-product and omega calculations in the index-two branch.
The multiplication formula retains the two ambient subgroup embeddings.
This is an intermediate output, not a terminal centrality assumption. -/
structure TIGeometry (C R S : Subgroup G) where
  mover : G
  mem_commuting : mover ∈ C
  outside_centralizer : mover ∉ S
  square_mem : mover ^ 2 ∈ S
  index_two : S.relIndex C = 2
  generates : S ⊔ zpowers mover = C
  disjoint : Disjoint R (R.conjBy mover)
  product : R × R.conjBy mover ≃* ↥(R ⊔ S)
  on_factors : ∀ (r : R) (q : R.conjBy mover), (product (r, q) : G) = (r : G) * q
  omega_fixed : omegaOneAmbient S =
    (omegaOneAmbient R ⊔ (omegaOneAmbient R).conjBy mover) ⊓
      centralizer ({mover} : Set G)
  omega_commutator : omegaOneAmbient S = ⁅omegaOneAmbient R, zpowers mover⁆

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.NormalFour
