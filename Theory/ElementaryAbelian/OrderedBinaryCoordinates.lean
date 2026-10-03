module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Ordered coordinates for an elementary group of order sixteen

Four generators of an elementary abelian two-group of order sixteen determine
an isomorphism with the binary four-space, taking each supplied generator to
the corresponding standard basis vector.

Binary words in the generators define a homomorphism from the binary four-space.
Its range contains the generators, so it is surjective; equality of the finite
orders makes it bijective. Inverting it retains the original ordered frame.

This elementary basis argument is used in Parrott, *A characterization of the
Tits' simple group* (1972), pp.678–681.
-/

open Subgroup
open scoped IsMulCommutative

private def word {E : Type*} [Group E] (v : Fin 4 → E)
    (x : Multiplicative (Fin 4 → ZMod 2)) : E :=
  v 0 ^ (x.toAdd 0).val * v 1 ^ (x.toAdd 1).val *
    v 2 ^ (x.toAdd 2).val * v 3 ^ (x.toAdd 3).val

private def wordHom {E : Type*} [Group E] [IsElementaryAbelian 2 E]
    (v : Fin 4 → E) : Multiplicative (Fin 4 → ZMod 2) →* E where
  toFun := word v
  map_one' := by simp [word]
  map_mul' x y := by
    have hs (i : Fin 4) : v i * v i = 1 := by
      simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) (v i)
    have hp (i : Fin 4) (a b : ZMod 2) :
        v i ^ (a + b).val = v i ^ a.val * v i ^ b.val := by
      fin_cases a <;> fin_cases b
      · change v i ^ 0 = v i ^ 0 * v i ^ 0
        simp
      · change v i ^ 1 = v i ^ 0 * v i ^ 1
        simp
      · change v i ^ 1 = v i ^ 1 * v i ^ 0
        simp
      · change v i ^ 0 = v i ^ 1 * v i ^ 1
        simp [hs]
    change word v (Multiplicative.ofAdd (x.toAdd + y.toAdd)) = _
    simp only [word, toAdd_ofAdd, Pi.add_apply, hp]
    ac_rfl

/-- Four ordered generators of an elementary abelian group of order sixteen
are an ordered binary basis. -/
public theorem elementarySixteen_ordered_coordinates {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (v : Fin 4 → E) (hgen : closure (Set.range v) = ⊤) (hcard : Nat.card E = 16) :
    ∃ c : E ≃* Multiplicative (Fin 4 → ZMod 2),
      ∀ i, c (v i) = Multiplicative.ofAdd (Pi.single i 1) := by
  classical
  let φ := wordHom v
  have heval (i : Fin 4) : φ (Multiplicative.ofAdd (Pi.single i 1)) = v i := by
    have hv (i j : Fin 4) : ((Pi.single i 1 : Fin 4 → ZMod 2) j).val =
        if i = j then 1 else 0 := by
      fin_cases i <;> fin_cases j <;> decide
    change word v (Multiplicative.ofAdd (Pi.single i 1)) = v i
    simp only [word, toAdd_ofAdd, hv]
    fin_cases i <;> simp
  have hsurj : Function.Surjective φ := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hgen]
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨_, heval i⟩
  have hbij : Function.Bijective φ := by
    apply (Nat.bijective_iff_surjective_and_card _).mpr
    refine ⟨hsurj, ?_⟩
    rw [hcard, Nat.card_eq_fintype_card]
    decide
  let c := (MulEquiv.ofBijective φ hbij).symm
  refine ⟨c, fun i => ?_⟩
  apply c.symm.injective
  simpa [c] using (heval i).symm
