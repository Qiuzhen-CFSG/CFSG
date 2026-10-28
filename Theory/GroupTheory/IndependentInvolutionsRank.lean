module
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Theory.GroupTheory.CoordinateInversionFaithfulness
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases
/-!
# Two-rank from independent commuting involutions

Three commuting involutions which independently invert three noninvolutory
witnesses generate an elementary eight. The coordinate-action specialization
applies this to a faithful odd root chart. It is used for the literal
exceptional carriers in the A.2.12 rank-two inspection (printed p.36).
-/
public section
namespace IndependentInvolutions
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev E := Fin 3 → C2
private def binaryHom {H : Type*} [Group H] (g : H) (hg : g ^ 2 = 1) : C2 →* H where
  toFun a := if a = 1 then 1 else g
  map_one' := by simp
  map_mul' a b := by
    have cases2 : ∀ x : C2, x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide +kernel
    have hsum : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := rfl
    have hone : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide +kernel
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl <;>
      simp [hsum, hone, ← pow_two, hg]
variable {H : Type*} [Group H]
variable (d : Fin 3 → H) (hd : ∀ i, d i ^ 2 = 1)
  (hcomm : ∀ i j, Commute (d i) (d j))
private def hom : E →* H := MonoidHom.noncommPiCoprod (fun i => binaryHom (d i) (hd i)) (by
  intro i j _ a b
  change Commute (if a=1 then 1 else d i) (if b=1 then 1 else d j)
  split_ifs <;> simp [hcomm])
private theorem hom_formula (a : E) : hom d hd hcomm a =
    (if a 0=1 then 1 else d 0) * (if a 1=1 then 1 else d 1) *
      (if a 2=1 then 1 else d 2) := by
  have he : a = (Pi.mulSingle 0 (a 0) : E) * (Pi.mulSingle 1 (a 1) : E) *
      (Pi.mulSingle 2 (a 2) : E) := by
    funext i
    fin_cases i <;> simp
  conv_lhs => rw [he, map_mul, map_mul]
  simp only [hom, MonoidHom.noncommPiCoprod_mulSingle, binaryHom, MonoidHom.coe_mk,
    OneHom.coe_mk]
private theorem hom_injective (x : Fin 3 → H) (hx : ∀ i, (x i)⁻¹ ≠ x i)
    (hact : ∀ i j, MulAut.conj (d i) (x j) = if i=j then (x j)⁻¹ else x j) :
    Function.Injective (hom d hd hcomm) := by
  have hformula (a : E) (j : Fin 3) :
      MulAut.conj (hom d hd hcomm a) (x j) = if a j = 1 then x j else (x j)⁻¹ := by
    rw [hom_formula]
    have hc (a b : H) (z : H) : MulAut.conj (a*b) z = MulAut.conj a (MulAut.conj b z) := by
      simp only [MulAut.conj_apply, mul_inv_rev]
      group
    rw [hc, hc]
    by_cases h0 : a 0=1 <;> by_cases h1 : a 1=1 <;> by_cases h2 : a 2=1 <;>
      fin_cases j <;> simp [h0,h1,h2,hact, -MulAut.conj_apply]
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  funext i
  by_contra hi
  change a i ≠ 1 at hi
  have he := hformula a i
  rw [ha] at he
  simp only [MulAut.conj_apply, one_mul, inv_one, mul_one, if_neg hi] at he
  exact hx i he.symm

include hd hcomm in
/-- Three independently acting commuting involutions generate an elementary eight. -/
theorem three_le [Finite H] (x : Fin 3 → H) (hx : ∀ i, (x i)⁻¹ ≠ x i)
    (hact : ∀ i j, MulAut.conj (d i) (x j) = if i=j then (x j)⁻¹ else x j) :
    3 ≤ primeRank 2 H := by
  apply primeRank_ge_of_elementary_embedding (f := hom d hd hcomm)
  · intro a
    funext i
    change (2:ℕ) • (a i).toAdd = 0
    rw [nsmul_eq_mul]
    change (2 : ZMod 2) * (a i).toAdd = 0
    rw [show (2 : ZMod 2) = 0 by decide +kernel, zero_mul]
  · simp [E,C2]
  · exact hom_injective d hd hcomm x hx hact

/-- Independent coordinate inversions give a faithful elementary eight. -/
theorem three_le_of_coordinate_actors [Finite H]
    {I A : Type*} [DecidableEq I] [CommGroup A]
    (j : (I → A) →* H) (hj : Function.Injective j) (v : A) (hv : v⁻¹ ≠ v)
    (d : I → H) (hd : ∀ i, d i ^ 2 = 1) (hc : ∀ i k, Commute (d i) (d k))
    (ha : ∀ i a, MulAut.conj (d i) (j a) = j (CoordinateInversion.invertCoordinate i a))
    (f : Fin 3 → I) (hf : Function.Injective f) : 3 ≤ primeRank 2 H := by
  apply three_le (fun i => d (f i)) (fun i => hd (f i)) (fun i k => hc (f i) (f k))
    (fun i => j (Pi.mulSingle (f i) v))
  · intro i h
    have he := hj ((map_inv j _).trans h)
    have hh := congrFun he (f i)
    exact hv (by simpa using hh)
  · intro i k
    rw [ha]
    have he : CoordinateInversion.invertCoordinate (f i) (Pi.mulSingle (f k) v) =
        if i=k then (Pi.mulSingle (f k) v : I → A)⁻¹ else Pi.mulSingle (f k) v := by
      funext l
      by_cases hik : i=k
      · subst k
        simp [CoordinateInversion.invertCoordinate]
        by_cases hl : l=f i <;> simp [hl]
      · have hfi : f i ≠ f k := fun h => hik (hf h)
        by_cases hl : l=f k
        · subst l
          simp [CoordinateInversion.invertCoordinate, hik, Ne.symm hfi]
        · simp [CoordinateInversion.invertCoordinate, hik, hl]
    rw [he]
    split_ifs <;> simp
end IndependentInvolutions
