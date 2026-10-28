module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

/-!
# Four-groups in odd-characteristic GL₂

Every elementary abelian subgroup of order four contains the scalar involution
`-I`, and consequently its image in PGL₂ is not faithful. A determinant-one
involution equals its adjugate, hence is scalar in dimension two. Avoiding
`-I` would therefore make the determinant injective on the four-group,
contradicting cyclicity of finite subgroups of the multiplicative group of a field.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §13.1,
printed p.876 (the two final four-group obstructions).
-/

namespace Matrix.GeneralLinearGroup

/-- In odd characteristic, the only determinant-one matrices squaring to one
in dimension two are the two scalar matrices. -/
public theorem eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one {F : Type*} [Field F] (hF : (2 : F) ≠ 0)
    (a : GL (Fin 2) F) (ha : a ^ 2 = 1) (hd : a.det = 1) : a = 1 ∨ a = -1 := by
  have hs : a.val * a.val = 1 := by simpa [pow_two] using congrArg Units.val ha
  have hd' : a.val.det = 1 := congrArg Units.val hd
  have hadj : a.val = a.val.adjugate := by
    calc
      a.val = a.val * (a.val * a.val.adjugate) := by rw [Matrix.mul_adjugate, hd']; simp
      _ = a.val.adjugate := by rw [← mul_assoc, hs, one_mul]
  have h00 := congrFun (congrFun hadj 0) 0
  have h01 := congrFun (congrFun hadj 0) 1
  have h10 := congrFun (congrFun hadj 1) 0
  rw [Matrix.adjugate_fin_two] at h00 h01 h10
  change a.val 0 0 = a.val 1 1 at h00
  change a.val 0 1 = -a.val 0 1 at h01
  change a.val 1 0 = -a.val 1 0 at h10
  have hz01 : a.val 0 1 = 0 := by
    apply (mul_eq_zero.mp (show (2 : F) * a.val 0 1 = 0 by linear_combination h01)).resolve_left hF
  have hz10 : a.val 1 0 = 0 := by
    apply (mul_eq_zero.mp (show (2 : F) * a.val 1 0 = 0 by linear_combination h10)).resolve_left hF
  have hsq : a.val 0 0 ^ 2 = 1 := by
    simpa [Matrix.det_fin_two, hz01, hz10, ← h00, sq] using hd'
  rcases sq_eq_one_iff.mp hsq with h | h
  · left; apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      simp [hz01, hz10, ← h00, h]
  · right; apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      simp [hz01, hz10, ← h00, h]

/-- Every faithful two-dimensional representation of a four-group in odd
characteristic contains the scalar involution. -/
public theorem exists_neg_one_of_four_group {F E : Type*} [Field F] [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hF : (2 : F) ≠ 0) (hE : Nat.card E = 4)
    (f : E →* GL (Fin 2) F) (hf : Function.Injective f) :
    ∃ a : E, f a = -1 := by
  by_contra hn
  push Not at hn
  let d := Matrix.GeneralLinearGroup.det.comp f
  have hd : Function.Injective d := by
    apply (MonoidHom.ker_eq_bot_iff d).mp
    apply d.ker.eq_bot_iff_forall.mpr
    intro a ha
    have hs : f a ^ 2 = 1 := by
      rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) a, map_one]
    rcases eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF (f a) hs ha with h | h
    · exact hf (h.trans f.map_one.symm)
    · exact (hn a h).elim
  have hc : IsCyclic E := isCyclic_of_injective_ringHom
    ((Units.coeHom F).comp d) (Units.val_injective.comp hd)
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) hE hc

/-- Every elementary abelian subgroup of order four in GL₂ contains `-I`. -/
public theorem neg_one_mem_of_four_group {F : Type*} [Field F]
    (hF : (2 : F) ≠ 0) (A : Subgroup (GL (Fin 2) F))
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4) : (-1 : GL (Fin 2) F) ∈ A := by
  let : Finite A := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨a, ha⟩ := exists_neg_one_of_four_group hF hA A.subtype A.subtype_injective
  exact ha ▸ a.property

/-- A four-group in GL₂ has a nonfaithful projective image. -/
public theorem not_injective_projective_of_four_group {F : Type*} [Field F]
    (hF : (2 : F) ≠ 0) (A : Subgroup (GL (Fin 2) F))
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4) :
    ¬ Function.Injective (Matrix.ProjGenLinGroup.mk.comp A.subtype) := by
  intro hi
  let a : A := ⟨-1, neg_one_mem_of_four_group hF A hA⟩
  have hs : scalar (Fin 2) (-1 : Fˣ) = (-1 : GL (Fin 2) F) := by
    apply Units.ext
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar, h]
  have he : (Matrix.ProjGenLinGroup.mk.comp A.subtype) a =
      (Matrix.ProjGenLinGroup.mk.comp A.subtype) 1 := by
    change Matrix.ProjGenLinGroup.mk (-1 : GL (Fin 2) F) = _
    rw [← hs, Matrix.ProjGenLinGroup.mk_scalar, map_one]
  have h := congrArg (fun b : A => (b : GL (Fin 2) F).val 0 0) (hi he)
  have hn : (-1 : F) = 1 := by simpa [a] using h
  exact hF (by linear_combination -hn)

end Matrix.GeneralLinearGroup
