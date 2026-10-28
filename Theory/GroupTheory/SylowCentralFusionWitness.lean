module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Local witnesses for fusion of a central involution

Glauberman's elementary fusion lemma selects a subgroup Q of a Sylow
two-subgroup T and an odd-order element normalizing both Q and C_T(Q)
that moves the given central involution. The selection can either contain
Z(T), or lie in the normal closure of the involution. These are different
selections: the two extra conclusions are not required of a single Q.

This module specifies the witnesses used in the two parts of Glauberman,
“On the automorphism group of a finite group having no non-identity normal
subgroups of odd order”, Math. Z. 93 (1966), Lemma 1, pp.155–156.
It does not assert existence of the witnesses. The normal-closure bound is
the consequence of clause (e′) needed in the automorphism application.
-/

public section

namespace SylowCentralFusion
open Subgroup

universe u
variable {G : Type u} [Group G]

/-- The common local data in Glauberman's two fusion selections. -/
structure Witness (T : Sylow 2 G) (z : G) where
  subgroup : Subgroup G
  mover : G
  le_sylow : subgroup ≤ (T : Subgroup G)
  mem_subgroup : z ∈ subgroup
  normalizer_sylow : ∃ R : Sylow 2 (normalizer (subgroup : Set G)),
    (R : Subgroup (normalizer (subgroup : Set G))).map
      (normalizer (subgroup : Set G)).subtype =
        (T : Subgroup G) ⊓ normalizer (subgroup : Set G)
  normalizes : mover ∈ normalizer (subgroup : Set G)
  normalizes_centralizer : mover ∈ normalizer
    (((T : Subgroup G) ⊓ centralizer (subgroup : Set G)) : Set G)
  odd_order : Odd (orderOf mover)
  moves : mover * z * mover⁻¹ ≠ z

/-- The elementary fusion input, with separate center-containing and
normal-closure-contained witnesses. This is a proof obligation, not an axiom. -/
@[expose] def CentralInvolutionFusion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (z : G),
    orderOf z = 2 → z ∈ (T : Subgroup G) →
    (∀ t ∈ (T : Subgroup G), t * z = z * t) →
    (∃ g : G, g * z * g⁻¹ ∈ (T : Subgroup G) ∧ g * z * g⁻¹ ≠ z) →
    (∃ w : Witness T z, (center T).map (T : Subgroup G).subtype ≤ w.subgroup) ∧
    (∃ w : Witness T z, w.subgroup ≤ normalClosure ({z} : Set G))

end SylowCentralFusion
