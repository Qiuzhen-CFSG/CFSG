module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.ModuleFacts
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.ModuleSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer.Algebra

/-!
# The contrary configuration and intermediate targets for MS93 (4.3)

A counterexample retains an arbitrary critical pair and the vertex exactly
two steps before its endpoint. The groups R and R_0 in the printed proof
are actual commutators. The set nu(a) uses the genuine quotient-fixed
preimage B_a; edge displacement means [Z_a,T_t].

The intermediate structures below are conclusions still to be constructed.
They separate (4.3.1), (4.3.2), and the independent transfer (4.2)(i), without
assuming CommonFacts or hiding (4.3) in an input. Every use in the final
assembly must discharge these intermediate targets.

Source: Meierfrankenfeld--Stellmacher (1993), pp.881--890.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape
variable {M : Type*} [Group M] {R : Subgroup M}

/-- A vertex on a shortest path, specified by its distance from the endpoint. -/
def Before (a a' c : Vertex R) (n : ℕ) : Prop :=
  (cosetGraph R).dist c a' = n ∧
    (cosetGraph R).dist a c + n = (cosetGraph R).dist a a'

/-- The actual contrary assumption at the start of (4.3). -/
structure Counterexample (geometry : Geometry R) where
  a : Vertex R
  a' : Vertex R
  c : Vertex R
  color_a : color R a = false
  critical : CriticalPair R a a' (geometry.exists_critical a color_a)
  before : Before a a' c 2
  trapped : V R a ≤ Q R c

/-- The edge module denoted U_t^a on printed p.881. -/
noncomputable def edgeDisplacement (a t : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⁅Z R a, Q R t⁆

/-- The source's nu(a), with exact distance two, not the whole radius-two ball. -/
def movingNeighbors (geometry : Geometry R) (a : Vertex R) : Set (Vertex R) :=
  {d | (cosetGraph R).dist a d = 2 ∧ ¬ Z R d ≤ B R a (geometry.Z_normal a)}

/-- Source R = [Z_alpha,Z_alpha']. -/
noncomputable def criticalCommutator (a a' : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⁅Z R a, Z R a'⁆

/-- Source R_0 = [V_alpha,Z_alpha'], distinct from the global core. -/
noncomputable def radiusCommutator (a a' : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⁅V R a, Z R a'⁆

/-- The full expanded c(A/N)=1 statement inside the actual vertex group. -/
structure NaturalSectionAt (a : Vertex R) (A N : Subgroup (FreeAmalgam R)) where
  local_group : A ≤ stabilizer R a
  kernel_le : N ≤ A
  projection : stabilizer R a →* SL
  module_section : SingleNaturalSection projection ((Q R a).subgroupOf (stabilizer R a))
    (pResidual 2 (stabilizer R a)) (A.subgroupOf (stabilizer R a))
    (N.subgroupOf (stabilizer R a))

/-- All seven assertions of (4.3.1), in the binary specialization.
The marked natural section in (iii) includes the triple commutator and split
fixed/moving quotient, as specified in ModuleSection. -/
structure InitialFacts {geometry : Geometry R} (p : Counterexample geometry) where
  radius_eq_edge : ∀ t, Before p.a p.a' t 1 →
    radiusCommutator p.a p.a' = edgeDisplacement p.a' t
  radius_card : Nat.card (radiusCommutator p.a p.a') = 4
  critical_card : Nat.card (criticalCommutator p.a p.a') = 2
  critical_index : (Q R p.a').relIndex (Z R p.a) = 2
  natural_section : NaturalSectionAt p.a (V R p.a) (Z R p.a)
  moving_generation : ∀ d ∈ movingNeighbors geometry p.a,
    Vcirc R p.a ≤ NormalizerTransfer.conjugatesIn (Z R d) (stabilizer R p.a)
  six_le : 6 ≤ geometry.b R
  radius_moving_card : 4 ≤ Nat.card (⁅V R p.a, Vcirc R p.c⁆ : Subgroup (FreeAmalgam R))
  H_card : 4 ≤ Nat.card (H R p.a)
  edge_commutator : ∀ t, Before p.a' p.a t 1 →
    ∀ d, Adjacent R d t → d ∈ movingNeighbors geometry p.a →
      ⁅Z R d, Q R p.a⁆ = edgeDisplacement d t

/-- The two conclusions of (4.3.2). Their proof requires the genuine (1.7)
pairing, not just natural-module recognition. -/
structure LocalControl {geometry : Geometry R} (p : Counterexample geometry) : Prop where
  commutator_le_fixed : ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a
  H_eq_edge : ∀ t, Before p.a' p.a t 1 →
    ∀ d, Adjacent R d t → d ∈ movingNeighbors geometry p.a →
      H R p.a = ⁅Z R d, Q R p.a⁆ ∧ H R p.a = edgeDisplacement d t

/-- The general (4.2)(i) transfer. It does not assume a critical distance of four. -/
def EdgeTransfer (geometry : Geometry R) : Prop :=
  ∀ a t, color R a = false → Adjacent R a t →
    (∀ d, Adjacent R d t → edgeDisplacement d t ≤ B R a (geometry.Z_normal a)) →
      edgeDisplacement a t ≤ Z R t

/-- The center of the actual finite local stabilizer, included in the amalgam. -/
def localCenter (a : Vertex R) : Subgroup (FreeAmalgam R) :=
  (center (stabilizer R a)).map (stabilizer R a).subtype

/-- The actual group W(t) from (4.3.6); the reverse nu condition is essential. -/
noncomputable def backwardSpan (geometry : Geometry R) (a t : Vertex R) :
    Subgroup (FreeAmalgam R) :=
  ⨆ d, ⨆ (_ : Adjacent R d t), ⨆ (_ : a ∈ movingNeighbors geometry d), V R d

/-- The actual conjugates mu and lambda chosen in (4.3.8) and reused in the
final contradiction. The three supplied vertices are alpha'-4, alpha'-3,
and alpha'-5, respectively; their path equations are premises of the producer. -/
structure PropagationWitnesses {geometry : Geometry R} (p : Counterexample geometry)
    (d t₃ t₅ : Vertex R) where
  mu : Vertex R
  lam : Vertex R
  first_conjugator : FreeAmalgam R
  second_conjugator : FreeAmalgam R
  first_local : first_conjugator ∈ stabilizer R p.c
  second_local : second_conjugator ∈ stabilizer R d
  first_image : act R first_conjugator p.a' = mu
  second_image : act R second_conjugator mu = lam
  first_adjacent : Adjacent R mu t₃
  second_adjacent : Adjacent R lam t₅
  first_not_moving : mu ∉ movingNeighbors geometry d
  first_displacement : radiusCommutator p.a p.a' = edgeDisplacement mu t₃
  second_displacement : radiusCommutator p.a p.a' = edgeDisplacement lam t₅
  first_intersection : radiusCommutator p.a p.a' = U R mu ⊓ localCenter d
  second_intersection : radiusCommutator p.a p.a' = U R lam ⊓ localCenter d

/-- The propagation conclusions (4.3.3)--(4.3.8), still to be proved from
the preceding stages. The fields retain each chosen critical pair and path;
products mean the subgroup join together with the required local normality.
The terminal radius-four statements do not assert the final escape theorem. -/
structure PropagationFacts (geometry : Geometry R) : Prop where
  edge_indices : ∀ p : Counterexample geometry, ∀ t, Before p.a' p.a t 1 →
    (Z R t).relIndex (Z R p.a) = 2 ∧ (Q R p.a).relIndex (Q R t) = 4
  equal_Z : ∀ p : Counterexample geometry, ∀ t, Before p.a' p.a t 1 →
    ∀ d e, Adjacent R d t → Adjacent R e t →
      ¬ U R d ⊓ Z R e ≤ localCenter e → Z R d = Z R e
  moving_Z_unique : ∀ p : Counterexample geometry, ∀ t, Before p.a' p.a t 1 →
    ∃ d, Adjacent R d t ∧ d ∈ movingNeighbors geometry p.a ∧
      ∀ e, Adjacent R e t → e ∈ movingNeighbors geometry p.a → Z R e = Z R d
  six_lt : ∀ _p : Counterexample geometry, 6 < geometry.b R
  backward_bound : ∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
    ¬ radiusCommutator p.a p.a' ≤ localCenter d →
      d ∈ movingNeighbors geometry p.c ∧
      ∀ t, Adjacent R p.a t →
        (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a →
          backwardSpan geometry p.a t ≤ Q R d
  product_normal : ∀ p : Counterexample geometry, ∀ d,
    (cosetGraph R).dist p.a d = 2 → p.a ∈ movingNeighbors geometry d →
      V R d ⊔ V R p.a ≤ stabilizer R p.a ∧
      ((V R d ⊔ V R p.a).subgroupOf (stabilizer R p.a)).Normal ∧
      ⁅V R d, Ltilde R p.a⁆ ≤ Vcirc R p.a
  moving_symmetric : ∀ p : Counterexample geometry, ∀ d,
    d ∈ movingNeighbors geometry p.a ↔ p.a ∈ movingNeighbors geometry d
  far_not_moving : ∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
    p.c ∉ movingNeighbors geometry d
  moving_radius_bound : ∀ p : Counterexample geometry,
    ∀ d ∈ movingNeighbors geometry p.a, V R d ≤ Q R p.c
  radius_central : ∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
    radiusCommutator p.a p.a' ≤ localCenter p.c ⊓ localCenter d
  witnesses : ∀ p : Counterexample geometry, ∀ d t₃ t₅,
    Before p.a p.a' d 4 → Before p.a p.a' t₃ 3 → Before p.a p.a' t₅ 5 →
      Nonempty (PropagationWitnesses p d t₃ t₅)
  radius_four : ∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
    (¬ VBall R p.a 4 ≤ Q R d) ∧ VBall R p.a 4 ⊓ Q R d ≤ Q R p.c ∧
      ∀ t, Before p.a' p.a t 1 → VBall R d 4 ⊔ Q R p.a = Q R t

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape
