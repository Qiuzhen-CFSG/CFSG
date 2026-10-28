module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticEncoding

/-!
# Finite tests for anisotropy and balanced fibres

The packed coefficient code and the sixteen encoded vectors retain the exact
hypotheses of the binary quadratic normal-form problem. In particular, the
balanced condition counts all three nonzero fibres and is not replaced by
anisotropy alone. This is the finite input to the MacWilliams unitary normal
form (Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3).
-/

namespace MacWilliamsSylow.QuadraticCertificate

@[expose] public def anisotropic (n : Fin 1048576) : Bool := decide (
  ∀ x : Fin 16, coordinateSquare (coefficients n) (vector x) = 1 → x = 0)

@[expose] public def balanced (n : Fin 1048576) : Bool := decide (
  ∀ z : Fin 4, z ≠ 0 →
    (Finset.univ.filter fun x : Fin 16 =>
      coordinateSquare (coefficients n) (vector x) = central z).card = 5)

public theorem anisotropic_of_hypothesis (n : Fin 1048576)
    (ha : ∀ x, coordinateSquare (coefficients n) x = 1 → x = 1) :
    anisotropic n = true := by
  apply decide_eq_true
  intro x hx
  apply vector_bijective.1
  simpa only [vector_zero] using ha _ hx

public theorem balanced_of_hypothesis (n : Fin 1048576)
    (hb : ∀ z : BinaryCoordinates 2, z ≠ 1 →
      Nat.card {v : BinaryCoordinates 4 // coordinateSquare (coefficients n) v = z} = 5) :
    balanced n = true := by
  apply decide_eq_true
  intro z hz
  have hcz : central z ≠ 1 := by
    intro h
    apply hz
    apply central_bijective.1
    simpa only [central_zero] using h
  let e : Fin 16 ≃ BinaryCoordinates 4 := Equiv.ofBijective vector vector_bijective
  let e' : {x : Fin 16 // coordinateSquare (coefficients n) (vector x) = central z} ≃
      {v : BinaryCoordinates 4 // coordinateSquare (coefficients n) v = central z} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  have hc := (Nat.card_congr e').trans (hb _ hcz)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hc

end MacWilliamsSylow.QuadraticCertificate
