module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.CoordinateModel

/-!
# Pointwise centralizers of totally singular planes

Two distinct nonidentity vectors in a totally singular plane, together with
their product, are singular. In the two-definite-plane coordinates, an actor
fixing both vectors and preserving each definite plane is the identity.
The finite calculation below checks this directly in the literal wreath
action, using kernel reduction.

For the actual subgroup, the quadratic comparison and conjugation
compatibility transfer this calculation to the plane-swap homomorphism.
Its kernel is exactly the relative centralizer of the whole natural module.
The index formula therefore bounds the subgroup's order by twice the order
of that relative centralizer. This concerns pointwise fixation, not setwise
stabilization of the singular plane.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
contradiction in the proof of 15.3.46(4), printed p.1141.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization

open Subgroup
attribute [local instance] orthogonalAction
private instance : DecidableEq OrthogonalActor :=
  fun a b => decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    RegularWreathProduct.ext_iff.symm
private instance : Fintype OrthogonalActor :=
  Fintype.ofEquiv ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
    (RegularWreathProduct.equivProd _ _).symm

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem eq_one_of_fixing_singular_pair_of_shift_one :
    ∀ v w : OrthogonalVector, v ≠ 1 → w ≠ 1 → v ≠ w →
      orthogonalCoordinateValue v = 0 → orthogonalCoordinateValue w = 0 →
      orthogonalCoordinateValue (v * w) = 0 →
      ∀ a : OrthogonalActor, a.right = 1 → a • v = v → a • w = w → a = 1 := by
  decide +kernel

variable {G : Type*} [Group G] [Finite G]
  {M V P : Subgroup G} [IsElementaryAbelian 2 V]

/-- The pointwise centralizer of an actual totally singular plane has image
of order at most two in the natural orthogonal action. -/
theorem card_le_two_mul_card_inf_centralizer_of_totallySingular
    (d : NaturalOrthogonalAction M V) (k : OrthogonalCoordinateModel d P)
    {B X : Subgroup G} (hs : IsTotallySingular d.form B) (hB : Nat.card B = 4)
    (hXM : X ≤ M) (hXB : X ≤ centralizer (B : Set G)) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ centralizer (V : Set G) : Subgroup G) := by
  classical
  let := Fintype.ofFinite B
  have hBc : Fintype.card B = 4 := by rwa [Nat.card_eq_fintype_card] at hB
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {1}) (t := Finset.univ (α := B)) (by simp [hBc])
  have hb1 : b ≠ 1 := by simpa using hb
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {1, b}) (t := Finset.univ (α := B)) (by simp [Ne.symm hb1, hBc])
  have hc1 : c ≠ 1 ∧ c ≠ b := by simpa using hc
  let e : B →* OrthogonalVector :=
    k.action.coordinates.toMonoidHom.comp (inclusion hs.1)
  have hei : Function.Injective e :=
    k.action.coordinates.injective.comp (inclusion_injective hs.1)
  have heb : e b ≠ 1 := fun h => hb1 (hei (h.trans e.map_one.symm))
  have hec : e c ≠ 1 := fun h => hc1.1 (hei (h.trans e.map_one.symm))
  have hebc : e b ≠ e c := fun h => hc1.2 (hei h).symm
  have hsing (u : B) : orthogonalCoordinateValue (e u) = 0 := by
    rw [show e u = k.action.coordinates (inclusion hs.1 u) from rfl, ← k.form_eq]
    exact hs.2 _ u.property
  have hfix (x : X) (u : B) :
      k.action.actor (inclusion hXM x) • e u = e u := by
    change k.action.actor (inclusion hXM x) •
      k.action.coordinates (inclusion hs.1 u) = k.action.coordinates (inclusion hs.1 u)
    rw [← k.action.compatible]
    apply congrArg k.action.coordinates
    apply Subtype.ext
    change (x : G) * (u : G) * (x : G)⁻¹ = u
    exact mul_inv_eq_iff_eq_mul.mpr ((hXB x.property u u.property).symm)
  let f : X →* OrthogonalPlaneIndex :=
    RegularWreathProduct.rightHom.comp (k.action.actor.comp (inclusion hXM))
  have he : f.ker = (X ⊓ centralizer (V : Set G)).subgroupOf X := by
    ext x
    change f x = 1 ↔ (x : G) ∈ X ⊓ centralizer (V : Set G)
    constructor
    · intro hx
      have hid := eq_one_of_fixing_singular_pair_of_shift_one (e b) (e c) heb hec hebc (hsing b) (hsing c)
        (by rw [← map_mul]; exact hsing (b * c)) _ hx (hfix x b) (hfix x c)
      have hm : inclusion hXM x ∈ k.action.actor.ker := hid
      rw [k.action.ker_actor] at hm
      exact ⟨x.property, hm⟩
    · intro hx
      have hm : inclusion hXM x ∈ k.action.actor.ker := by
        rw [k.action.ker_actor]
        exact hx.2
      change RegularWreathProduct.rightHom (k.action.actor (inclusion hXM x)) = 1
      rw [show k.action.actor (inclusion hXM x) = 1 from hm, map_one]
  have hi : (X ⊓ centralizer (V : Set G)).relIndex X ≤ 2 := by
    change ((X ⊓ centralizer (V : Set G)).subgroupOf X).index ≤ 2
    rw [← he, index_ker]
    have hc := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
    exact hc.trans_eq (by norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card])
  have hmul := ((X ⊓ centralizer (V : Set G)).subgroupOf X).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left (a := X)
    (b := centralizer (V : Set G)))).toEquiv] at hmul
  change Nat.card (X ⊓ centralizer (V : Set G) : Subgroup G) *
    (X ⊓ centralizer (V : Set G)).relIndex X = Nat.card X at hmul
  nlinarith

end CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization
