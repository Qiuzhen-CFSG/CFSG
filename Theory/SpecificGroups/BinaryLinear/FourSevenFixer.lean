module
public import Theory.Alternating.Aut
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Mathlib.GroupTheory.Perm.Centralizer
/-!
# Involutory automorphisms fixing a seven-element in PSL₄(2)

Use the actual exceptional equivalence PSL₄(2) ≃ A₈ and the conjugation
isomorphism S₈ ≃ Aut(A₈). A seven-element is a single seven-cycle on eight
letters, whose symmetric centralizer has order seven. Its pointwise fixer
therefore contains no nonidentity involution.

The point-component application in Aschbacher--Smith 10.2.9, printed
pp.750--751, uses an element of order seven in the literal image of L₃(2).
The exceptional comparison retains the attribution in its imported module.
-/

public section
open Subgroup Equiv.Perm
open scoped MatrixGroups
namespace BinaryLinear.FourSevenFixer

/-- The pointwise fixer of a seven-element in Aut(A₈) has no involution. -/
theorem alternating_fixing_seven (x : alternatingGroup (Fin 8)) (hx : orderOf x = 7)
    (a : MulAut (alternatingGroup (Fin 8))) (ha : a ^ 2 = 1) (hfix : a x = x) : a = 1 := by
  let e : Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide))
  let y := e.symm a
  have hy2 : y ^ 2 = 1 := by
    dsimp [y]
    rw [← map_pow, ha, map_one]
  have hyC : y ∈ centralizer ({(x : Equiv.Perm (Fin 8))} : Set (Equiv.Perm (Fin 8))) := by
    apply mem_centralizer_singleton_iff.mpr
    have he : (e y) x = x := (e.apply_symm_apply a) ▸ hfix
    have hh := congrArg (fun z : alternatingGroup (Fin 8) => (z : Equiv.Perm (Fin 8))) he
    change y * (x : Equiv.Perm (Fin 8)) * y⁻¹ = x at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have ho : orderOf (x : Equiv.Perm (Fin 8)) = 7 := (orderOf_coe x).trans hx
  have hc : Nat.card (centralizer ({(x : Equiv.Perm (Fin 8))} :
      Set (Equiv.Perm (Fin 8)))) = 7 := by
    have hcy : (x : Equiv.Perm (Fin 8)).IsCycle :=
      isCycle_of_prime_order' (ho ▸ by decide) (by simp [ho])
    rw [nat_card_centralizer, hcy.cycleType, ← hcy.orderOf, ho]
    norm_num
  have h7 : orderOf y ∣ 7 := hc ▸
    (centralizer ({(x : Equiv.Perm (Fin 8))} : Set (Equiv.Perm (Fin 8)))).orderOf_dvd_natCard hyC
  have hy : y = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 7)
      (orderOf_dvd_of_pow_eq_one hy2) h7)
  have he := congrArg e hy
  simpa only [y, e.apply_symm_apply, map_one] using he

/-- The actual PSL₄(2) carrier has the same seven-element fixer obstruction. -/
theorem eq_one_of_fixes_seven (x : PSL(4, ZMod 2)) (hx : orderOf x = 7)
    (a : MulAut PSL(4, ZMod 2)) (ha : a ^ 2 = 1) (hfix : a x = x) : a = 1 := by
  let e := Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  apply (MulAut.congr e).injective
  rw [map_one]
  apply alternating_fixing_seven (e x) (by rw [e.orderOf_eq]; exact hx)
    (MulAut.congr e a) (by rw [← map_pow, ha, map_one])
  simpa only [MulAut.congr_apply, MulEquiv.trans_apply, e.symm_apply_apply] using congrArg e hfix
end BinaryLinear.FourSevenFixer
