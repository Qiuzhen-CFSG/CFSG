module

public import Theory.SpecificGroups.MacWilliams.HallJankoCenter

/-!
# Executable coordinates for the Hall–Janko Sylow presentation

The seven normal-word bits form an executable group of order 128, isomorphic
to the presented group. Right multiplication by a generator is certified by
collection in the presentation. The certified bijective normal-word map transfers
associativity without a large cubic check. The normal-word API comes from `HallJankoCenter`;
this extension supplies the executable group structure.

Source: the power-commutator presentation in `SylowPresentations`, following
MacWilliams, Trans. AMS 150 (1970), and Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3, p.386. Finite certificates use kernel reduction only.
-/

namespace MacWilliamsSylow.HallJankoCoordinates

/-- The seven binary coordinates, in the order of the presentation generators. -/
@[ext] public structure Code where
  toFin : Fin 128

public instance : DecidableEq Code := fun a b =>
  if h : a.toFin = b.toFin then isTrue (Code.ext h)
  else isFalse (fun hab => h (congrArg Code.toFin hab))

public instance : Fintype Code := Fintype.ofEquiv (Fin 128)
  ⟨Code.mk, Code.toFin, fun _ => rfl, fun _ => rfl⟩
public instance : OfNat Code 0 := ⟨⟨0⟩⟩
public instance (n : ℕ) : OfNat Code (n + 2) := ⟨⟨OfNat.ofNat (n + 2)⟩⟩
public instance : Inhabited Code := ⟨0⟩

open HallJankoCalculation

/-- Multiplication collects the right normal word into the left one. -/
@[expose] public def multiply (n m : Code) : Code :=
  ⟨(normal m.toFin).foldl (fun a i => right i a) n.toFin⟩

private theorem repr_fold (w : List (Fin 7)) (n : Fin 128) :
    representative (w.foldl (fun a i => right i a) n) =
      representative n * word (generator hallJankoTable) w := by
  induction w generalizing n with
  | nil => simp [word]
  | cons i w ih =>
    rw [List.foldl_cons, ih, ← repr_right]
    simp [word, mul_assoc]

private def repr (n : Code) : HallJankoSylow := representative n.toFin

private theorem repr_bijective : Function.Bijective repr := by
  constructor
  · intro a b h
    exact Code.ext (representative_bijective.injective h)
  · intro x
    obtain ⟨n, hn⟩ := representative_bijective.surjective x
    exact ⟨⟨n⟩, hn⟩

private theorem repr_multiply (n m : Code) :
    repr (multiply n m) = repr n * repr m :=
  repr_fold (normal m.toFin) n.toFin

/-- Reverse the normal word and cube each generator to invert it. -/
@[expose] public def inverse (n : Code) : Code :=
  ⟨(normal n.toFin).foldr (fun i a => right i (right i (right i a))) 0⟩

set_option maxRecDepth 10000 in
private theorem inverse_mul : ∀ n : Code, multiply (inverse n) n = 0 := by
  decide +kernel

public instance : Group Code where
  one := 0
  mul := multiply
  inv := inverse
  mul_assoc a b c := by
    apply repr_bijective.injective
    change repr (multiply (multiply a b) c) = repr (multiply a (multiply b c))
    simp only [repr_multiply, mul_assoc]
  one_mul a := by
    apply repr_bijective.injective
    change repr (multiply 0 a) = repr a
    rw [repr_multiply]
    exact one_mul _
  mul_one a := by
    apply repr_bijective.injective
    change repr (multiply a 0) = repr a
    rw [repr_multiply]
    exact mul_one _
  inv_mul_cancel := by exact inverse_mul

/-- The coordinate group realizes exactly the specified presentation. -/
public noncomputable def equiv : Code ≃* HallJankoSylow := by
  let f : Code →* HallJankoSylow :=
    { toFun := repr, map_one' := repr_zero, map_mul' := repr_multiply }
  exact MulEquiv.ofBijective f repr_bijective

/-- The concrete realization sends a code to its collected generator word. -/
public theorem equiv_apply (n : Code) :
    equiv n = word (generator hallJankoTable) (normal n.toFin) := by rfl

/-- The identity code is zero. -/
public theorem one_eq_zero : (1 : Code) = 0 := by rfl

/-- Multiplication is the executable collection formula. -/
public theorem mul_eq_multiply (n m : Code) : n * m = multiply n m := by rfl

/-- Inversion is the executable reverse-word formula. -/
public theorem inv_eq_inverse (n : Code) : n⁻¹ = inverse n := by rfl

/-- The coordinate group has exactly 128 elements. -/
public theorem card : Nat.card Code = 128 := by
  exact (Nat.card_congr (show Code ≃ Fin 128 from
    ⟨Code.toFin, Code.mk, fun _ => rfl, fun _ => rfl⟩)).trans (Nat.card_fin 128)

end MacWilliamsSylow.HallJankoCoordinates
