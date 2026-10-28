module

public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.StemData
public import Theory.GroupTheory.Commutator.ThirdHom
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two

/-!
# Vanishing of scalar-fixed central stem kernels

A marked additive-field abelianization lets every homomorphism to a
commutative group descend through the coordinate. Applying this in three
variables to the central third commutator produces a scalar-invariant triple
map: its values lie in the specified kernel, which the scalars fix. Triple-map
vanishing therefore puts the derived subgroup in the center.

The norm over the field units on that center, composed with the commutator
pairing and descended through the same coordinate, is a scalar-invariant
pairing. Pairing vanishing kills the norm on the whole derived subgroup.
On the specified kernel the norm is the odd power given by the number of
field units; this power is injective on a two-group. Thus the kernel vanishes.
No finiteness hypothesis on the ambient group is needed.

The two invariant-map predicates remain explicit independent field inputs.
This is the central-defect step of the ordinary Suzuki multiplier argument
in Aschbacher--Smith I.1.3 (printed p.407), GLS3 §6.1, using standard central
commutator calculus. `DefectVanishing.lean` applies it to the literal canonical
Suzuki covering, whose local stem data is constructed in `LocalCover.lean`.
-/

open scoped commutatorElement IsMulCommutative
open Subgroup

namespace ScalarInvariantMaps.StemData
variable {F P : Type} [Field F] [Group P] (d : StemData F P)

private noncomputable def descend {C : Type} [CommGroup C] :
    (P →* C) →* (Multiplicative F →* C) where
  toFun f := d.coordinate.liftOfSurjective d.coordinate_surjective
    ⟨f, d.coordinate_ker ▸ Abelianization.commutator_subset_ker f⟩
  map_one' := by
    apply MonoidHom.ext
    intro a
    obtain ⟨x, rfl⟩ := d.coordinate_surjective a
    simp only [MonoidHom.liftOfRightInverse_comp_apply, MonoidHom.one_apply]
  map_mul' f g := by
    apply MonoidHom.ext
    intro a
    obtain ⟨x, rfl⟩ := d.coordinate_surjective a
    simp only [MonoidHom.mul_apply, MonoidHom.liftOfRightInverse_comp_apply]

@[simp] private theorem descend_coordinate {C : Type} [CommGroup C] (f : P →* C) (x : P) :
    descend d f (d.coordinate x) = f x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

private noncomputable def descendPair {C : Type} [CommGroup C] :
    (P →* (P →* C)) →* (Multiplicative F →* (Multiplicative F →* C)) :=
  (descend d).comp (MonoidHom.compHom (descend d))

@[simp] private theorem descendPair_coordinate {C : Type} [CommGroup C]
    (f : P →* (P →* C)) (x y : P) :
    descendPair d f (d.coordinate x) (d.coordinate y) = f x y := by
  simp [descendPair]

private noncomputable def descendTriple {C : Type} [CommGroup C]
    (f : P →* (P →* (P →* C))) :
    Multiplicative F →* (Multiplicative F →* (Multiplicative F →* C)) :=
  descend d ((descendPair d).comp f)

@[simp] private theorem descendTriple_coordinate {C : Type} [CommGroup C]
    (f : P →* (P →* (P →* C))) (x y z : P) :
    descendTriple d f (d.coordinate x) (d.coordinate y) (d.coordinate z) = f x y z := by
  simp [descendTriple]

include d in
/-- Vanishing of scalar-invariant triple maps makes the marked stem group
nilpotent of class at most two. -/
public theorem commutator_le_center_of_triples (h₃ : TriplesVanish.{0,0} F) :
    _root_.commutator P ≤ center P := by
  obtain ⟨f, hf⟩ := exists_third_commutator_hom
    (d.third_le_kernel.trans d.kernel_le_center)
  let b := descendTriple d f
  have hb : b = 1 := h₃ (center P) b (by
    intro t a v c
    obtain ⟨x, rfl⟩ := d.coordinate_surjective a
    obtain ⟨y, rfl⟩ := d.coordinate_surjective v
    obtain ⟨z, rfl⟩ := d.coordinate_surjective c
    simp only [← d.coordinate_action, b, descendTriple_coordinate]
    apply Subtype.ext
    rw [hf, hf, ← map_commutatorElement, ← map_commutatorElement]
    exact d.action_kernel t _ (d.third_le_kernel
      (commutator_mem_commutator
        (commutator_mem_commutator (mem_top x) (mem_top y)) (mem_top z))))
  have hz (x y z : P) : ⁅⁅x,y⁆,z⁆ = 1 := by
    have h := congrArg (fun B => ((B (d.coordinate x) (d.coordinate y)
      (d.coordinate z) : center P) : P)) hb
    simpa only [b, descendTriple_coordinate, hf, MonoidHom.one_apply, coe_one] using h
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  exact mem_center_iff.mpr (fun z =>
    (commutatorElement_eq_one_iff_mul_comm.mp (hz x y z)).symm)

private def centralPairing (hc : _root_.commutator P ≤ center P) :
    P →* (P →* center P) where
  toFun x := {
    toFun y := ⟨⁅x,y⁆, hc (commutator_mem_commutator (mem_top x) (mem_top y))⟩
    map_one' := Subtype.ext (by simp)
    map_mul' y z := by
      apply Subtype.ext
      change ⁅x,y*z⁆ = ⁅x,y⁆ * ⁅x,z⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have h := mem_center_iff.mp
        (hc (commutator_mem_commutator (mem_top x) (mem_top z))) y
      calc
        _ = ⁅x,y⁆ * (y * ⁅x,z⁆ * y⁻¹) := by simp only [mul_assoc]
        _ = _ := by rw [h, mul_inv_cancel_right] }
  map_one' := by ext y; simp
  map_mul' x y := by
    ext z
    change ⁅x*y,z⁆ = ⁅x,z⁆ * ⁅y,z⁆
    rw [commutatorElement_mul_left_eq_conj_mul]
    have h := mem_center_iff.mp
      (hc (commutator_mem_commutator (mem_top y) (mem_top z)))
    rw [h x, mul_inv_cancel_right]
    exact (h ⁅x,z⁆).symm

private noncomputable def centerNorm [Fintype Fˣ] : center P →* center P where
  toFun z := ∏ t : Fˣ, centerCongr (d.action t) z
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]

private theorem centerNorm_invariant [Fintype Fˣ] (t : Fˣ) (z : center P) :
    centerNorm d (centerCongr (d.action t) z) = centerNorm d z := by
  change (∏ s : Fˣ, centerCongr (d.action s) (centerCongr (d.action t) z)) =
    ∏ s : Fˣ, centerCongr (d.action s) z
  apply Fintype.prod_equiv (Equiv.mulRight t)
  intro s
  apply Subtype.ext
  change d.action s (d.action t z) = d.action (s*t) z
  rw [map_mul]
  rfl

private theorem centerNorm_kernel [Fintype Fˣ] (x : P) (hx : x ∈ d.kernel) :
    centerNorm d ⟨x, d.kernel_le_center hx⟩ =
      (⟨x, d.kernel_le_center hx⟩ : center P) ^ Fintype.card Fˣ := by
  have h (t : Fˣ) : centerCongr (d.action t) ⟨x, d.kernel_le_center hx⟩ =
      (⟨x, d.kernel_le_center hx⟩ : center P) :=
    Subtype.ext (d.action_kernel t x hx)
  change (∏ t : Fˣ, centerCongr (d.action t) ⟨x, d.kernel_le_center hx⟩) = _
  simp only [h, Finset.prod_const, Finset.card_univ]

private theorem two_coprime_card_units [Fintype F] [DecidableEq F] [CharP F 2] :
    Nat.Coprime 2 (Fintype.card Fˣ) := by
  classical
  rw [Fintype.card_units, Nat.coprime_two_left, Nat.odd_iff]
  have h := FiniteField.even_card_of_char_two (ringChar.eq F 2)
  have hp := Fintype.card_pos (α := F)
  omega

include d in
private theorem norm_eq_one_on_commutator [Fintype Fˣ]
    (h₂ : PairingsVanish.{0,0} F) (hc : _root_.commutator P ≤ center P)
    (x : P) (hx : x ∈ _root_.commutator P) :
    centerNorm d ⟨x, hc hx⟩ = 1 := by
  let q := centralPairing hc
  let b := descendPair d (q.compr₂ (centerNorm d))
  have hb : b = 1 := h₂ (center P) b (by
    intro t a v
    obtain ⟨y, rfl⟩ := d.coordinate_surjective a
    obtain ⟨z, rfl⟩ := d.coordinate_surjective v
    simp only [← d.coordinate_action, b, descendPair_coordinate, MonoidHom.compr₂_apply]
    have he : q (d.action t y) (d.action t z) = centerCongr (d.action t) (q y z) := by
      apply Subtype.ext
      exact (map_commutatorElement (d.action t) y z).symm
    rw [he, centerNorm_invariant])
  have hcomm (y z : P) : centerNorm d (q y z) = 1 := by
    have h := congrArg (fun B => B (d.coordinate y) (d.coordinate z)) hb
    simpa only [b, descendPair_coordinate, MonoidHom.compr₂_apply,
      MonoidHom.one_apply] using h
  have hderived : _root_.commutator P ≤
      (centerNorm d).ker.map (center P).subtype := by
    apply Subgroup.commutator_le.mpr
    intro y _ z _
    exact ⟨q y z, hcomm y z, rfl⟩
  obtain ⟨z, hz, he⟩ := hderived hx
  have he' : z = (⟨x, hc hx⟩ : center P) := Subtype.ext he
  exact he' ▸ hz

/-- A scalar-fixed central two-group in the derived subgroup vanishes if
all scalar-invariant pairings and triple maps on the marked field vanish. -/
public theorem kernel_eq_bot_of_invariants [Finite F] [CharP F 2]
    (h₂ : PairingsVanish.{0,0} F) (h₃ : TriplesVanish.{0,0} F) : d.kernel = ⊥ := by
  classical
  let _ := Fintype.ofFinite F
  have hc := d.commutator_le_center_of_triples h₃
  apply bot_unique
  intro x hx
  have hn := norm_eq_one_on_commutator d h₂ hc x (d.kernel_le_commutator hx)
  rw [centerNorm_kernel d x hx] at hn
  have hp : (⟨x, hx⟩ : d.kernel) ^ Fintype.card Fˣ = 1 :=
    Subtype.ext (congrArg (fun z : center P => (z : P)) hn)
  have he : (⟨x, hx⟩ : d.kernel) = 1 := by
    apply (d.kernel_isTwoGroup.powEquiv (two_coprime_card_units (F := F))).injective
    simpa only [IsPGroup.powEquiv_apply, one_pow] using hp
  exact congrArg Subtype.val he

end ScalarInvariantMaps.StemData
