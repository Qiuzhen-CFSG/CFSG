module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A marked original orthogonal critical pair

The four-dimensional space in 14.6.13 and 14.6.17 is the moved section
[U_H,H]/Z. Its coordinates must intertwine the actual H-conjugation action
with the two-plane matrix wreath action, and its actor kernel is the original
Q_H. An abstract isomorphism with an orthogonal group is insufficient.

This module specifies that common construction target, defines its two
covering planes, and computes their order from the actual quotient map.
The critical-pair record retains one conjugator on all original labels.
It is an input contract: this module makes no existence or classification
claim about the original H.

Source: Aschbacher--Smith 14.6.13(1) and 14.6.17(1--5),
printed pp.1031--1032 and 1035--1036.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03
variable {G : Type*} [Group G]

/-- The orthogonal action on the literal moved quotient, with its actual
two-core as actor kernel. All conjugations are left conjugations. -/
structure SourceOrthogonalFourAction (H U Z Q : Subgroup G) where
  normalized : H ≤ normalizer (U : Set G)
  point_le : Z ≤ ⁅U,H⁆
  actor : H →* OrthogonalActor
  onto : Function.Surjective actor
  actor_kernel : actor.ker = Q.subgroupOf H
  coordinates : (⁅U,H⁆ : Subgroup G) →* OrthogonalVector
  surjective : Function.Surjective coordinates
  vector_kernel : coordinates.ker = Z.subgroupOf ⁅U,H⁆
  compatible : letI := orthogonalAction
    ∀ (h : H) (v : (⁅U,H⁆ : Subgroup G)),
      coordinates (⁅U,H⁆.normalizerMonoidHom
        ⟨h,normalizer_commutator_ge_right U H h.property⟩ v) =
          actor h • coordinates v

namespace SourceOrthogonalFourAction
variable {H U Z Q : Subgroup G} (d : SourceOrthogonalFourAction H U Z Q)

/-- The preimage of a definite binary plane in the actual moved group. -/
def plane (i : OrthogonalPlaneIndex) : Subgroup G :=
  ((orthogonalCoordinatePlane i).comap d.coordinates).map ⁅U,H⁆.subtype

theorem plane_le (i : OrthogonalPlaneIndex) : d.plane i ≤ ⁅U,H⁆ := map_subtype_le _

theorem point_le_plane (i : OrthogonalPlaneIndex) : Z ≤ d.plane i := by
  intro z hz
  have hzk : (⟨z,d.point_le hz⟩ : (⁅U,H⁆ : Subgroup G)) ∈ d.coordinates.ker := by
    rw [d.vector_kernel]
    exact hz
  refine mem_map.mpr ⟨⟨z,d.point_le hz⟩,?_,rfl⟩
  change d.coordinates ⟨z,d.point_le hz⟩ ∈ orthogonalCoordinatePlane i
  rw [show d.coordinates ⟨z,d.point_le hz⟩ = 1 from hzk]
  exact one_mem _

/-- The covering plane has order eight, rather than the quotient's order four. -/
theorem card_plane [Finite G] (hZ : Nat.card Z = 2) (i : OrthogonalPlaneIndex) :
    Nat.card (d.plane i) = 8 := by
  let A := (orthogonalCoordinatePlane i).comap d.coordinates
  let f : A →* orthogonalCoordinatePlane i :=
    (d.coordinates.comp A.subtype).codRestrict _ (fun x => x.property)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := d.surjective y
    exact ⟨⟨x,show d.coordinates x ∈ orthogonalCoordinatePlane i from hx ▸ y.property⟩,
      Subtype.ext hx⟩
  have hk : f.ker = d.coordinates.ker.subgroupOf A := by
    ext x
    exact Subtype.ext_iff
  have hKA : d.coordinates.ker ≤ A := by
    intro x hx
    change d.coordinates x ∈ orthogonalCoordinatePlane i
    rw [show d.coordinates x = 1 from hx]
    exact one_mem _
  have hker : Nat.card f.ker = 2 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hKA).toEquiv,d.vector_kernel,
      Nat.card_congr (subgroupOfEquivOfLe d.point_le).toEquiv,hZ]
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    orthogonalCoordinatePlane_card,hker] at hc
  change Nat.card (A.map ⁅U,H⁆.subtype) = 8
  rw [card_map_of_injective ⁅U,H⁆.subtype_injective,hc]

end SourceOrthogonalFourAction

/-- The first alternative of 14.6.13 with the actual conjugator and chosen plane.
The nontrivial quotient commutator is stated as failure of containment in Z. -/
structure SourceOrthogonalCriticalPair {H U Z Q : Subgroup G}
    (d : SourceOrthogonalFourAction H U Z Q) (Mc : Subgroup G) where
  first : OrthogonalPlaneIndex
  g : G
  outside : g ∉ Mc
  normalizes : U.map (MulAut.conj g).toMonoidHom ≤
    H ⊓ normalizer (d.plane first : Set G)
  reverse : U ≤ H.map (MulAut.conj g).toMonoidHom
  noncentral : ¬ ⁅d.plane first,U.map (MulAut.conj g).toMonoidHom⁆ ≤ Z

end CFSG.Quasithin.Chapter14.Section06
