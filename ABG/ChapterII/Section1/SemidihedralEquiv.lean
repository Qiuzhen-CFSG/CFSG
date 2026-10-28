module
public import Stellmacher.MainDefs

/-!
# Transport of the semidihedral presentation

A multiplicative equivalence preserves the actual semidihedral presentation,
including its cardinality, generator orders, conjugation relation, and
generation assertion. This lower-level API is shared by the fusion-frame
transport and embedded quaternion-layer arguments of ABG Chapter II.
It is extracted unchanged from the original Section 2 frame transport.
-/

namespace ABG

/-- The semidihedral presentation is preserved by multiplicative equivalences. -/
public theorem semidihedral_equiv {G K : Type*} [Group G] [Group K]
    (e : G ≃* K) (hG : Stellmacher.IsSemidihedralGroup G) :
    Stellmacher.IsSemidihedralGroup K := by
  obtain ⟨n, hn, hc, a, b, ha, hb, hab, hgen⟩ := hG
  refine ⟨n, hn, (Nat.card_congr e.toEquiv).symm.trans hc, e a, e b,
    (e.orderOf_eq a).trans ha, (e.orderOf_eq b).trans hb, ?_, ?_⟩
  · simpa only [map_mul, map_inv, map_pow] using congrArg e hab
  · have hmap := congrArg (Subgroup.map e.toMonoidHom) hgen
    simpa only [MonoidHom.map_closure, MulEquiv.coe_toMonoidHom, Set.image_pair,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] using hmap

end ABG

