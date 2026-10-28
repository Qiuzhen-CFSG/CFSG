module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.Basic
public import Theory.Representation.PSL3Two.DoubledParabolic

/-!
# One doubled-natural marking of the actual commutator module

K acts on U_K = [W_K,K]. Its existing star-to-plus quotient gives the
literal component map, which is surjective. `DoubledCoordinates` records
one choice of compatible actor and module identifications. Restriction to
any subgroup of K retains this same intertwiner.

The record asserts no parabolic image, no split-point geometry, and no
noncentrality. Constructing it under hypothetical centrality is the
B.5.1/B.5.6 application still needed in the source assembly.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
13.6.14 and 13.6.20, printed pp.929 and 931.
-/

@[expose] public section
open Subgroup Representation BinaryLinearThree
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction
open ComponentSelection
variable {G : Type*} [_root_.Group G]

/-- The component acts on its literal commutator module. -/
theorem K_normalizes_UK (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    K ≤ normalizer (UK K L T z v : Set G) := by
  intro k hk
  rw [mem_normalizer_iff_map_conj_eq, UK, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp
      (plusActor_normalizes_WK K L T z v hL hz (K_le_plusActor K L T v hk)),
    mem_normalizer_iff_map_conj_eq.mp (K.le_normalizer hk)]

/-- The existing star-to-plus map restricted to the original K. -/
noncomputable def componentPlus (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    K →* plusImage K L T z v hL hz K :=
  (componentStarToPlus K L T z v hK hL hz).comp (starImageMap z v K hK)

theorem componentPlus_surjective (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Function.Surjective (componentPlus K L T z v hK hL hz) :=
  (componentStarToPlus_surjective K L T z v hK hL hz).comp
    (starImageMap_surjective z v K hK)

theorem componentPlus_apply (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (k : K) :
    (componentPlus K L T z v hK hL hz k : Gplus K L T z v hL hz) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k) :=
  componentStarToPlus_mk K L T z v hK hL hz k

/-- A single identification of the actual commutator module and its component
actor. This is module data, with no parabolic or commutator geometry asserted. -/
structure DoubledCoordinates (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) where
  actor : plusImage K L T z v hL hz K ≃* BinaryLinearThree.Group
  moduleEquiv : UK K L T z v ≃* Multiplicative (Vector × Vector)
  equivariant : ∀ (k : K) (u : UK K L T z v),
    moduleEquiv (conjugationAction _ _ (K_normalizes_UK K L T z v hL hz) k u) =
      Multiplicative.ofAdd ((W.prod W) (actor (componentPlus K L T z v hK hL hz k))
        (Multiplicative.toAdd (moduleEquiv u)))

namespace DoubledCoordinates
variable {K L T : Subgroup G} {z v : G}
    {hK : K ≤ Gv v} {hL : Tv T v ≤ normalizer (Lv L v : Set G)}
    {hz : Tv T v ≤ centralizer ({z} : Set G)}

/-- The literal action map into SL₃(2) belonging to this marking. -/
noncomputable def actionMap (d : DoubledCoordinates K L T z v hK hL hz) :
    K →* BinaryLinearThree.Group :=
  d.actor.toMonoidHom.comp (componentPlus K L T z v hK hL hz)

theorem actionMap_surjective (d : DoubledCoordinates K L T z v hK hL hz) :
    Function.Surjective d.actionMap :=
  d.actor.surjective.comp (componentPlus_surjective K L T z v hK hL hz)

/-- Restriction preserves the chosen equivariance, without changing coordinates. -/
theorem equivariant_restrict (d : DoubledCoordinates K L T z v hK hL hz)
    (P : Subgroup G) (hPK : P ≤ K) (p : P) (u : UK K L T z v) :
    d.moduleEquiv (conjugationAction _ P
        (hPK.trans (K_normalizes_UK K L T z v hL hz)) p u) =
      Multiplicative.ofAdd ((W.prod W) (d.actionMap (inclusion hPK p))
        (Multiplicative.toAdd (d.moduleEquiv u))) := by
  exact d.equivariant (inclusion hPK p) u

end DoubledCoordinates
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction
