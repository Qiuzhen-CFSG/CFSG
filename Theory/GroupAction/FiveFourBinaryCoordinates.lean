module

public import Theory.GroupAction.FiveFourBinaryModel
public import Theory.GroupAction.FiveFourBinaryLeftCoordinates
public import Theory.ElementaryAbelian.BinaryPairingDuality

/-!
# Compatible coordinates for paired five-four actions

A choice of binary coordinates on the first group of a nondegenerate pairing
between elementary abelian groups of equal order determines coordinates on the
second group. Finite binary duality identifies each group with the dual of the
other; composing this identification with the model intersection pairing gives
the second coordinate equivalence.

Invariance of both pairings then transports every intertwined operator to the
second group. In particular, translation and the quarter-turn on the first
group give compatible coordinates on both groups. If the quarter-turn actor
has the same square as a supplied element, its square acts by the model
involution on the second group.

For a faithful five-four action on groups of order sixteen, the left-coordinate
existence theorem supplies these operators, so the construction gives compatible
coordinates while preserving the square of the supplied order-four element.

Source: the paired binary actions underlying Parrott, *A characterization of
the Tits' simple group* (1972),
`refs/original/n-group-global/parrott-tits-characterization-1972.pdf`,
printed pp.673–674.
-/

open scoped IsMulCommutative
namespace Theory.GroupAction.FiveFourBinaryModel

private def modelPairingHom : Space →* (Space →* Multiplicative (ZMod 2)) where
  toFun x := {
    toFun := pairing x
    map_one' := by revert x; decide +kernel
    map_mul' := pairing_mul.2 x }
  map_one' := by apply MonoidHom.ext; intro x; change pairing 1 x = 1; revert x; decide +kernel
  map_mul' x y := by apply MonoidHom.ext; intro z; exact pairing_mul.1 x y z

private theorem modelPairingHom_injective : Function.Injective modelPairingHom := by
  apply modelPairingHom.ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  apply pairing_nondegenerate.1 x
  intro y
  exact congrArg (fun f : Space →* Multiplicative (ZMod 2) => f y) hx

private theorem modelPairingHom_flip_bijective : Function.Bijective modelPairingHom.flip := by
  let : IsElementaryAbelian 2 Space := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel) }
  exact modelPairingHom.binary_pairing_flip_bijective rfl modelPairingHom_injective

/-- A coordinate system on one side uniquely determines compatible coordinates
on the other side of a perfect binary pairing. -/
public theorem exists_right_coordinates
    {A V W : Type*} [Group A] [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (d : BinaryQuadraticPairing A V W) (hcard : Nat.card V = Nat.card W)
    (left : V ≃* Space) :
    ∃ right : W ≃* Space, ∀ v w, d.pairing v w = pairing (left v) (right w) := by
  let e := MulEquiv.ofBijective d.pairing.flip
    (d.pairing.binary_pairing_flip_bijective hcard d.pairing_injective)
  let c : (V →* Multiplicative (ZMod 2)) ≃* (Space →* Multiplicative (ZMod 2)) :=
    left.monoidHomCongrLeft
  let m := MulEquiv.ofBijective modelPairingHom.flip modelPairingHom_flip_bijective
  let right : W ≃* Space := (e.trans c).trans m.symm
  refine ⟨right, ?_⟩
  intro v w
  have hh : modelPairingHom.flip (right w) = c (e w) := m.apply_symm_apply _
  have hh' := congrArg (fun f : Space →* Multiplicative (ZMod 2) => f (left v)) hh
  simpa [modelPairingHom, c, e] using hh'.symm

private theorem pairing_right_ext {x y : Space}
    (h : ∀ z, pairing z x = pairing z y) : x = y := by
  apply modelPairingHom_flip_bijective.1
  exact MonoidHom.ext h

/-- Pairing-compatible coordinates automatically intertwine any operator that
preserves the model pairing and is intertwined on the first side. -/
private theorem right_intertwines
    {A V W : Type*} [Group A] [Group V] [Group W]
    (d : BinaryQuadraticPairing A V W)
    (left : V ≃* Space) (right : W ≃* Space)
    (hp : ∀ v w, d.pairing v w = pairing (left v) (right w))
    (a : A) (T : Space → Space)
    (hT : ∀ x y, pairing (T x) (T y) = pairing x y)
    (hleft : ∀ v, left (d.leftAction a v) = T (left v)) :
    ∀ w, right (d.rightAction a w) = T (right w) := by
  intro w
  apply pairing_right_ext
  intro x
  obtain ⟨v, rfl⟩ := (left.surjective.comp (d.leftAction a).surjective) x
  change pairing (left (d.leftAction a v)) (right (d.rightAction a w)) =
    pairing (left (d.leftAction a v)) (T (right w))
  rw [← hp, d.pairing_equivariant, hp, hleft, hT]

/-- Left coordinates and actors with the prescribed square extend to compatible
coordinates for both actions. The right action is forced by duality. -/
public theorem coordinates_of_left
    {A V W : Type*} [Group A] [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (d : BinaryQuadraticPairing A V W) (hcard : Nat.card V = Nat.card W)
    (g : A) (left : V ≃* Space) (t s : A)
    (ht : ∀ v, left (d.leftAction t v) = translate (left v))
    (hs : ∀ v, left (d.leftAction s v) = turn (left v))
    (hsquare : s ^ 2 = g ^ 2) : Nonempty (Coordinates d g) := by
  obtain ⟨right, hp⟩ := exists_right_coordinates d hcard left
  have hrt := right_intertwines d left right hp t translate pairing_invariant.1 ht
  have hrs := right_intertwines d left right hp s turn pairing_invariant.2 hs
  refine ⟨{
    left := left
    right := right
    translationActor := t
    turnActor := s
    left_translate := ht
    right_translate := hrt
    left_turn := hs
    right_turn := hrs
    right_square := ?_
    pairing_eq := hp }⟩
  intro w
  rw [← hsquare, pow_two, map_mul]
  change right (d.rightAction s (d.rightAction s w)) = _
  rw [hrs, hrs]

end Theory.GroupAction.FiveFourBinaryModel

namespace Theory.GroupAction.BinaryQuadraticPairing

/-- A faithful five-four action on paired elementary groups of order sixteen
admits compatible binary coordinates for the supplied order-four actor. -/
public theorem exists_five_four_coordinates
    {V W : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hV : Nat.card V = 16) (hW : Nat.card W = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (d : BinaryQuadraticPairing
      (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) V W)
    (g : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) (hg : orderOf g = 4) :
    Nonempty (FiveFourBinaryModel.Coordinates d g) := by
  obtain ⟨left, t, s, ht, hs, hsquare⟩ :=
    exists_five_four_left_coordinates hV φ hφ d.leftAction d.leftAction_injective g hg
  exact FiveFourBinaryModel.coordinates_of_left d (hV.trans hW.symm)
    g left t s ht hs hsquare

end Theory.GroupAction.BinaryQuadraticPairing
