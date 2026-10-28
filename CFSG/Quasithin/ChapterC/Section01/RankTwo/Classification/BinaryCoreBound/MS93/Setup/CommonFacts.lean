module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Source
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Shared conditional interfaces for the two MS93 distance branches

`Geometry` is an output required of the setup constructor. `CommonFacts`
is a separate output required of the basic-reduction owner. Neither record
has a constructor from the original MS input in this file. In particular,
publishing these interfaces does not discharge those two proof obligations.

The natural module is an actual equivariant group isomorphism to the additive
binary three-space, with one automorphism of the specified matrix quotient.
The escape clause uses the vertex two steps before the critical endpoint,
characterized by distances along a geodesic. No center of the commutator core,
exponent, or distance-four/eight alternative is included.

Source: MS93 (1993), 2.1(i),(iv),(v), 2.2(i)--(iii), 4.1, 4.2(ii), 4.3,
printed pp.855--857, 881--890. Additional intermediate lemmas of Section 3
remain with the basic-reduction owner rather than being silently assumed here.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93

open Subgroup Stellmacher.PushingUp.AmalgamGraph

universe u
variable {M : Type u} [Group M] (R : Subgroup M)

/-- The critical geometry to be constructed on the actual infinite amalgam. -/
structure Geometry : Prop where
  tree : (cosetGraph R).IsTree
  exists_critical : ∀ a, color R a = false → ∃ n, CriticalRadius R a n
  even : ∀ a (ha : color R a = false),
    Even (criticalDistance R a (exists_critical a ha))
  distance_constant : ∀ a (ha : color R a = false),
    criticalDistance R a (exists_critical a ha) =
      criticalDistance R (alpha R) (exists_critical (alpha R) rfl)
  centralizes : ∀ a, color R a = false → ⁅Z R a, Q R a⁆ = ⊥
  omega_bound : ∀ a (ha : color R a = false),
    0 < criticalDistance R a (exists_critical a ha) → Z R a ≤ X R a
  Z_normal : ∀ a, ((Z R a).subgroupOf (stabilizer R a)).Normal
  V_local : ∀ a (ha : color R a = false),
    2 < criticalDistance R a (exists_critical a ha) → V R a ≤ stabilizer R a

namespace Geometry

noncomputable def b (geometry : Geometry R) : ℕ :=
  criticalDistance R (alpha R) (geometry.exists_critical (alpha R) rfl)

end Geometry

/-- The literal natural model at the distinguished M-vertex. The displayed
equation uses ambient conjugation through embedM, not an unrelated action. -/
structure NaturalU (π : M →* SL) where
  marking : SL ≃* SL
  equiv : U R (alpha R) ≃* Multiplicative (Fin 3 → ZMod 2)
  normalized : Mbar R ≤ normalizer (U R (alpha R) : Set (FreeAmalgam R))
  action : ∀ (m : M) (u v : U R (alpha R)),
    (v : FreeAmalgam R) = embedM R m * (u : FreeAmalgam R) * (embedM R m)⁻¹ →
    Multiplicative.toAdd (equiv v) =
      (marking (π m)).val.mulVec (Multiplicative.toAdd (equiv u))

/-- Common reduction outputs, to be proved before either source branch can
be applied unconditionally. All groups are the definitions from `Defs`. -/
structure CommonFacts {L : Subgroup M} (source : LocalSource L R)
    (geometry : Geometry R) where
  large_distance : 2 < geometry.b R
  centralizer : ∀ a t, color R a = false → Adjacent R a t →
    Q R t ⊓ Subgroup.centralizer (Z R a : Set (FreeAmalgam R)) = Q R a
  X_eq_Z : ∀ a, color R a = false → X R a = Z R a
  natural : NaturalU R source.projection
  full_commutation : ⁅U R (alpha R), Ltilde R (alpha R)⁆ = U R (alpha R)
  decomposition : Z R (alpha R) = U R (alpha R) ⊔
    (Z R (alpha R) ⊓ Subgroup.centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)))
  disjoint : Disjoint (U R (alpha R))
    (Z R (alpha R) ⊓ Subgroup.centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)))
  normalization_transfer : ∀ a, color R a = false →
    ∀ Y : Subgroup (FreeAmalgam R), Y ≤ Q R a →
      (Y.subgroupOf (stabilizer R a)).Normal →
      ⁅Vcirc R a, Y⁆ ≤ fixedCore R a → ⁅V R a, Y⁆ ≤ fixedCore R a
  X_bound : ∀ a (ha : color R a = false) a', color R a' = false →
    (cosetGraph R).dist a a' < criticalDistance R a (geometry.exists_critical a ha) →
    X R a ≤ Q R a'
  critical_noncommutation : ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) → ⁅Z R a, Z R a'⁆ ≠ ⊥
  critical_reverse : ∀ a (ha : color R a = false) a' (ha' : color R a' = false),
    CriticalPair R a a' (geometry.exists_critical a ha) →
    CriticalPair R a' a (geometry.exists_critical a' ha')
  escape : ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
    ∀ c, (cosetGraph R).dist c a' = 2 →
      (cosetGraph R).dist a c + 2 = (cosetGraph R).dist a a' → ¬ V R a ≤ Q R c

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
