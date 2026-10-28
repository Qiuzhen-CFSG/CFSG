module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Endgame
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Contracts for the marked graph-field model calculations

All groups below are actual subgroups of the source ambient group. The
normalizer equality uses Lᵣ = O²(C_L(r)), E = ⟨r,z⟩ and Q/E ≅ Q₈, with
normality only inside Q. The cover data specify the action of Q on E and
of C_Q(E) on Lᵣ. The centerless data retain an actual complement P and a
nonidentity Frattini involution with its conjugating element in L.

The placement predicate uses H/K for H = N_G(L), K = C_G(L), with K
restricted to H before taking the quotient. It concerns quaternion
subgroups centralizing the image of the specified outer involution.

These are shared contracts for independent calculations, not proofs of
their existence. Their construction and the exceptional-case assemblies
must discharge every field before source 16.4.9(2) is complete.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.1191–1192.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField

variable {G : Type*} [Group G] [Finite G]

/-- The marked normalizer N_LE(E) = LᵣQ and its actual quaternion quotient. -/
structure NormalizerData (L : Subgroup G) (r z : G) where
  Q : Subgroup G
  two_group : IsPGroup 2 Q
  four_le : fourGroup r z ≤ Q
  le_product : Q ≤ L ⊔ fourGroup r z
  normalizes_four : Q ≤ normalizer (fourGroup r z : Set G)
  normalizes_residual : Q ≤ normalizer (residual L r : Set G)
  normalizer_eq : (L ⊔ fourGroup r z) ⊓ normalizer (fourGroup r z : Set G) =
    residual L r ⊔ Q
  centralizer_eq : Q ⊓ centralizer (residual L r : Set G) = fourGroup r z
  residual_fixer : normalizer (L : Set G) ⊓ centralizer (residual L r : Set G) ≤
    (centralizer (L : Set G) ⊔ residual L r) ⊔ zpowers r
  quaternion :
    letI : ((fourGroup r z).subgroupOf Q).Normal :=
      normal_subgroupOf_of_le_normalizer normalizes_four
    Nonempty ((Q ⧸ (fourGroup r z).subgroupOf Q) ≃* QuaternionGroup 2)

/-- The transvection and irreducible cyclic-four action in the nontrivial-cover case. -/
structure CoverActionData {L : Subgroup G} {r z : G} (d : NormalizerData L r z) : Prop where
  fixes_z : d.Q ≤ centralizer ({z} : Set G)
  transvection : ∃ t ∈ d.Q, MulAut.conj t r = r * z
  cyclic_four :
    let C := d.Q ⊓ centralizer (fourGroup r z : Set G)
    letI : ((fourGroup r z).subgroupOf C).Normal :=
      normal_subgroupOf_of_le_normalizer (inf_le_left.trans d.normalizes_four)
    Nonempty ((C ⧸ (fourGroup r z).subgroupOf C) ≃* Multiplicative (ZMod 4))
  irreducible : ∀ A : Subgroup G, A ≤ residual L r →
    d.Q ⊓ centralizer (fourGroup r z : Set G) ≤ normalizer (A : Set G) →
      A = ⊥ ∨ A = residual L r

/-- The relative quotient H/K; no ambient normality of K is asserted. -/
abbrev actionQuotient (L : Subgroup G) :=
  normalizer (L : Set G) ⧸
    (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))

/-- The actual quotient homomorphism from the component normalizer. -/
def actionProjection (L : Subgroup G) :
    normalizer (L : Set G) →* actionQuotient L :=
  QuotientGroup.mk' ((centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)))

/-- The image of L in H/K, through its inclusion in H. -/
def innerImage (L : Subgroup G) : Subgroup (actionQuotient L) :=
  (L.subgroupOf (normalizer (L : Set G))).map (actionProjection L)

/-- The local quotient containment used on L′ and z in the centerless case. -/
def QuaternionPlacement (L : Subgroup G) : Prop :=
  ∀ s : normalizer (L : Set G), orderOf (s : G) = 2 →
    (s : G) ∉ centralizer (L : Set G) ⊔ L →
    ∀ P : Subgroup (actionQuotient L), Nonempty (P ≃* QuaternionGroup 2) →
      P ≤ centralizer ({actionProjection L s} : Set (actionQuotient L)) →
      P ≤ innerImage L ⊔ zpowers (actionProjection L s)

/-- The actual complement and Frattini fusion calculation; placement in L′E is separate. -/
structure CenterlessComplementData {L : Subgroup G} {r z : G}
    (d : NormalizerData L r z) where
  centralizes_four : d.Q ≤ centralizer (fourGroup r z : Set G)
  P : Subgroup G
  le_Q : P ≤ d.Q
  disjoint_four : Disjoint P (fourGroup r z)
  sup_four : P ⊔ fourGroup r z = d.Q
  quaternion : Nonempty (P ≃* QuaternionGroup 2)
  frattini_product : ∃ v ∈ (frattini P).map P.subtype,
    orderOf v = 2 ∧ v ∈ L ⊓ centralizer ({r} : Set G) ∧
    ∃ l ∈ L, MulAut.conj l r = r * v

end CFSG.Quasithin.Chapter16.Intersections.GraphField
