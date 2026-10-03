module
public import ABG.ChapterII.Section2.UnitaryOddCoefficientEquiv
public import Theory.FieldTheory.OddQuadraticCoefficientLift

/-!
# Unitary coordinates for a prescribed odd coefficient actor

Let E be a finite group of odd order with a prescribed injective action c
on GF(p^n), for p odd and n nonzero. There is an injective action cQ of
the same E on GF(p^(2n)) and an equivalence from the actual special-unitary
group to SL2(GF(p^n)) intertwining cQ with exactly the original c. The
intertwining is stated on the original underlying GL2 matrices, without
introducing an alternative action instance or changing the Hermitian form.

Lift the odd subgroup c.range to a quadratic coefficient subgroup A before
choosing any fixed-field coordinates. The odd-coefficient unitary theorem
then supplies coordinates b, an injective restriction r0, and an equivariant
special-unitary equivalence. The lift theorem applies to the same b. Its
restriction map agrees pointwise with r0 because their equations agree on
every element of the actual fixed field, so r0 has image exactly c.range.
Transport c through the inverse of r0's range equivalence and include A
in the quadratic automorphism group. Injectivity and the original actor
labels are preserved, giving the asserted exact intertwining.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pages 27-28,
the prescribed odd coefficient action in the unitary semilinear model.
This supplies the coefficient coordinates for the final Q-group assembly
and retains all odd fields, including orders three and nine.
-/

namespace ABG
open Matrix.GeneralLinearGroup

public theorem exists_unitary_coordinates_for_odd_actor
    {E : Type*} [Group E] [Finite E] (hE : Odd (Nat.card E))
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0)
    (c : E →* (GaloisField p n ≃+* GaloisField p n))
    (hc : Function.Injective c) :
    ∃ (cQ : E →* (GaloisField p (2 * n) ≃+* GaloisField p (2 * n)))
      (eSU : (unitaryForm 2 p n hn).specialSubgroup ≃*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n)),
      Function.Injective cQ ∧
      ∀ (e : E) (x y : (unitaryForm 2 p n hn).specialSubgroup),
        y.val = coefficientEquiv (cQ e) x.val →
          eSU y = GorensteinWalter.sl2RingEquiv (c e) (eSU x) := by
  classical
  have hD : Odd (Nat.card c.range) :=
    (Nat.card_congr (MonoidHom.ofInjective hc).toEquiv) ▸ hE
  obtain ⟨A, hA, hlift⟩ := GaloisField.exists_odd_quadratic_coefficient_lift p n hn c.range hD
  obtain ⟨b, r0, eSU, hr0, hres0, hinter⟩ :=
    exists_specialUnitary_equiv_sl2_of_odd_coefficients p n hp hn A hA
  obtain ⟨r, _, hrange, hres⟩ := hlift b
  have heq : r0 = r := by
    ext σ z
    apply b.symm.injective
    apply Subtype.ext
    have he := (hres0 σ (b.symm z)).symm.trans (hres σ (b.symm z))
    change (b.symm (r0 σ (b (b.symm z)))).val =
      (b.symm (r σ (b (b.symm z)))).val at he
    simpa only [b.apply_symm_apply] using he
  have hrange0 : r0.range = c.range := heq ▸ hrange
  let d : E →* r0.range := c.codRestrict r0.range
    (fun e => hrange0.symm ▸ (show c e ∈ c.range from ⟨e, rfl⟩))
  let l : E →* A := (MonoidHom.ofInjective hr0).symm.toMonoidHom.comp d
  have hrl (e : E) : r0 (l e) = c e := MonoidHom.apply_ofInjective_symm hr0 (d e)
  have hl : Function.Injective l := by
    intro e f hef
    apply hc
    rw [← hrl e, ← hrl f, hef]
  let cQ := A.subtype.comp l
  refine ⟨cQ, eSU, A.subtype_injective.comp hl, ?_⟩
  intro e x y hxy
  have h := hinter (l e) x y hxy
  rw [hrl] at h
  exact h

end ABG
