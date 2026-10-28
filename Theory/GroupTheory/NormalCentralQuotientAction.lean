module

public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Ring.Parity
/-!
# Conjugation on central quotients of normal subgroups

For characteristic `N` in a normal subgroup `L`, ambient conjugation induces an
actual homomorphism to `MulAut (L/N)`. The preimage of `Z(L/N)` is characteristic
and contains both `N` and `Z(L)`. The natural map from `L/Z(L)` to the quotient by
this preimage is surjective and equivariant; it is injective exactly when the
preimage equals `Z(L)`. The third isomorphism theorem identifies its target with
`(L/N)/Z(L/N)`.

This supplies the quotient interface in Aschbacher–Smith, *The Classification of
Quasithin Groups*, Corollary A.2.6, p. 34, where `N = O₂(L)`. It deliberately does
not identify the two central quotients without an additional hypothesis.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]
/-- Preimage of the center of the quotient by a normal subgroup. -/
@[expose] public def centralPreimage (N : Subgroup G) [N.Normal] : Subgroup G :=
  (center (G ⧸ N)).comap (QuotientGroup.mk' N)
public instance centralPreimage_normal (N : Subgroup G) [N.Normal] : (centralPreimage N).Normal :=
  inferInstanceAs ((center (G ⧸ N)).comap (QuotientGroup.mk' N)).Normal
public instance centralPreimage_characteristic (N : Subgroup G) [N.Characteristic] : (centralPreimage N).Characteristic :=
  Subgroup.Characteristic.comap_quotient_mk inferInstance
/-- The original normal subgroup lies in the central preimage. -/
public theorem le_centralPreimage (N : Subgroup G) [N.Normal] : N ≤ centralPreimage N := by
  intro n hn
  change QuotientGroup.mk' N n ∈ center (G ⧸ N)
  have hn' : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  rw [hn']
  exact one_mem _
/-- Central elements stay central in a quotient. -/
public theorem center_le_centralPreimage (N : Subgroup G) [N.Normal] :
    center G ≤ centralPreimage N := by
  intro z hz
  apply mem_center_iff.mpr
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact congrArg (QuotientGroup.mk' N) (mem_center_iff.mp hz g)
/-- The natural map from the central quotient to the central quotient after `N`. -/
public def centralQuotientProjection (N : Subgroup G) [N.Normal] :
    G ⧸ center G →* G ⧸ centralPreimage N :=
  QuotientGroup.lift (center G) (QuotientGroup.mk' (centralPreimage N)) (by
    rw [QuotientGroup.ker_mk']
    exact center_le_centralPreimage N)
@[simp] public theorem centralQuotientProjection_apply_mk (N : Subgroup G) [N.Normal]
    (g : G) : centralQuotientProjection N (QuotientGroup.mk' (center G) g) =
      QuotientGroup.mk' (centralPreimage N) g := by rfl

public theorem centralQuotientProjection_surjective (N : Subgroup G) [N.Normal] : Function.Surjective (centralQuotientProjection N) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective _) _
public theorem centralQuotientProjection_injective_iff (N : Subgroup G) [N.Normal] :
    Function.Injective (centralQuotientProjection N) ↔ center G = centralPreimage N := by
  exact (QuotientGroup.injective_lift_iff _ _ _).trans (by rw [QuotientGroup.ker_mk'])
variable (L : Subgroup G) [L.Normal] (N : Subgroup L) [N.Characteristic]
/-- Ambient conjugation on a characteristic quotient of a normal subgroup. -/
public def normalQuotientAction : G →* MulAut (L ⧸ N) :=
  (quotientAut N).comp MulAut.conjNormal
@[simp] public theorem normalQuotientAction_apply_mk (x : G) (l : L) :
    normalQuotientAction L N x (QuotientGroup.mk' N l) =
      QuotientGroup.mk' N (MulAut.conjNormal x l) := by
  exact quotientAut_apply_mk N (MulAut.conjNormal x) l
public theorem orderOf_normalQuotientAction_dvd (x : G) : orderOf (normalQuotientAction L N x) ∣ orderOf x :=
  orderOf_map_dvd _ _
public theorem odd_orderOf_normalQuotientAction (x : G) (hodd : Odd (orderOf x)) : Odd (orderOf (normalQuotientAction L N x)) :=
  hodd.of_dvd_nat (orderOf_map_dvd _ _)
public theorem centralQuotientProjection_equivariant (x : G) (q : L ⧸ center L) :
    centralQuotientProjection N (normalQuotientAction L (center L) x q) =
      normalQuotientAction L (centralPreimage N) x (centralQuotientProjection N q) := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center L) q
  simp only [normalQuotientAction_apply_mk, centralQuotientProjection_apply_mk]
/-- Elements of the normal subgroup induce inner automorphisms on its quotient. -/
public theorem normalQuotientAction_inner (l : L) : normalQuotientAction L N (l : G) =
    MulAut.conj (QuotientGroup.mk' N l) := by
  ext q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N q
  rw [normalQuotientAction_apply_mk]
  rw [MulAut.conjNormal_val]
  simp [MulAut.conj_apply]
/-- A genuinely outer quotient action can only come from outside the subgroup. -/
public theorem not_mem_of_normalQuotientAction_outer (x : G) (houter : normalQuotientAction L N x ∉
    (MulAut.conj : (L ⧸ N) →* MulAut (L ⧸ N)).range) : x ∉ L := by
  intro hx
  apply houter
  refine ⟨QuotientGroup.mk' N ⟨x, hx⟩, ?_⟩
  exact (normalQuotientAction_inner L N ⟨x, hx⟩).symm
end Subgroup
namespace Subgroup
variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
public theorem map_centralPreimage : (centralPreimage N).map (QuotientGroup.mk' N) = center (G ⧸ N) := by
  exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _
/-- The central quotient after dividing out `N`, expressed as one quotient. -/
public noncomputable def centralPreimageQuotientEquiv :
    G ⧸ centralPreimage N ≃* (G ⧸ N) ⧸ center (G ⧸ N) :=
  (QuotientGroup.quotientQuotientEquivQuotient N (centralPreimage N) (le_centralPreimage N)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N) _))
end Subgroup
