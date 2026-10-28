module

public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage.RootGroups
public import Theory.Representation.BinaryOffender.Defs

/-!
# Four concrete elementary actor candidates for PSL₂(11)

The elements t, s, u and l are images of the displayed determinant-one
matrices under SL₂ → SL₂/Z(SL₂). The automorphism d is the actual diagonal
action with parameter -1, including its action on the roots and t.
The candidates are the two cyclic groups and the inner and mixed four-groups.
`ActorCoverage` states the remaining exhaustive conjugacy assertion; this
module does not assert it.

These models support the finite-generation alternative to the PSL₂(11)
exclusion in Guralnick–Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript pp.8–9, and Aschbacher–Smith K.2, printed p.453.
-/

public section

open Matrix Subgroup
namespace Theory.PSL2.ElevenConjugateBudget
open OuterSolvable OuterSolvable.OddCoverage
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
abbrev F := ZMod 11
abbrev SL := SpecialLinearGroup (Fin 2) F
abbrev S := ProjectiveSpecialLinearGroup (Fin 2) F

@[expose] def slT : SL := ⟨!![0,1;-1,0], by decide⟩
@[expose] def slS : SL := ⟨!![1,3;3,-1], by decide⟩
abbrev slU : SL := SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one 1
abbrev slL : SL := SpecialLinearGroup.transvection (i := 1) (j := 0) one_ne_zero 1

@[expose] def t : S := quotientMap F slT
@[expose] def s : S := quotientMap F slS
@[expose] def u : S := quotientMap F slU
@[expose] def l : S := quotientMap F slL
@[expose] noncomputable def d : MulAut S := diagonalAutHom (-1 : Fˣ)
@[expose] def innerFour : Subgroup (MulAut S) := zpowers (MulAut.conj t) ⊔ zpowers (MulAut.conj s)
@[expose] noncomputable def outerFour : Subgroup (MulAut S) := zpowers (MulAut.conj t) ⊔ zpowers d

theorem t_conj_u : t * u * t⁻¹ = l⁻¹ := by
  simp only [t,u,l, ← map_mul, ← map_inv]
  apply congrArg (quotientMap F)
  decide

theorem d_sq : d * d = 1 := by
  change diagonalAutHom (-1 : Fˣ) * diagonalAutHom (-1 : Fˣ) = 1
  rw [← map_mul]
  simp

theorem d_u : d u = u⁻¹ := by
  rw [d,u, diagonalAutHom_apply_quotientMap, ← map_inv]
  apply congrArg (quotientMap F)
  decide

theorem d_l : d l = l⁻¹ := by
  rw [d,l, diagonalAutHom_apply_quotientMap, ← map_inv]
  apply congrArg (quotientMap F)
  decide

theorem t_sq : t ^ 2 = 1 := by
  rw [t, ← map_pow, ← map_one (quotientMap F)]
  apply (quotientMap_eq_iff _ _).mpr
  right
  decide

theorem t_ne_one : t ≠ 1 := by
  intro ht
  have h := (quotientMap_eq_iff slT 1).mp (by simpa [t] using ht)
  rcases h with h | h <;> revert h <;> decide

theorem s_sq : s ^ 2 = 1 := by
  rw [s, ← map_pow, ← map_one (quotientMap F)]
  apply (quotientMap_eq_iff _ _).mpr
  right
  decide

theorem t_s_commute : Commute t s := by
  change t * s = s * t
  simp only [t,s, ← map_mul]
  apply (quotientMap_eq_iff _ _).mpr
  right
  decide

theorem d_t : d t = t := by
  rw [d,t,diagonalAutHom_apply_quotientMap]
  apply (quotientMap_eq_iff _ _).mpr
  right
  decide

theorem d_ne_one : d ≠ 1 := by
  intro hd
  have he : u = u⁻¹ := by simpa only [hd, MulAut.one_apply] using d_u
  have h := (quotientMap_eq_iff slU slU⁻¹).mp (by simpa [u] using he)
  rcases h with h | h <;> revert h <;> decide

@[expose] noncomputable def actor : Fin 4 → Subgroup (MulAut S) :=
  ![zpowers (MulAut.conj t), zpowers d, innerFour, outerFour]

@[expose] def count : Fin 4 → ℕ := ![3,3,2,2]

/-- Exhaustive representative coverage, with conjugation in the actual automorphism group. -/
@[expose] def ActorCoverage : Prop := ∀ A : Subgroup (MulAut S),
  Representation.BinaryOffender.IsElementaryTwo A →
    ∃ (i : Fin 4) (a : MulAut S), A = (actor i).map (MulAut.congr a).toMonoidHom

end Theory.PSL2.ElevenConjugateBudget
