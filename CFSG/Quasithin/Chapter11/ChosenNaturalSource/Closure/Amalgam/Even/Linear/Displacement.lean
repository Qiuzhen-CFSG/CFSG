module
public import Theory.Representation.SemilinearInvolutionFixedCard
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

/-!
# Excluding field twists by natural displacement size

The fixed-cardinality theorem gives displacement order squared equal to
q³ for a nontrivial field-twisted involution. Thus displacement order is
strictly greater than q, including q=4. The source application to the
literal ambient commutator is in SmallCommutator.
Source: Aschbacher--Smith, 11.5.8, refs/quasithin.pdf, printed p.784.
-/

public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A field-twisted involution on the three-space has more than q displacements. -/
theorem semilinear_displacement_large (a : (Fin 3 → F) →+ (Fin 3 → F))
    (ha : Function.Involutive a) (σ : F ≃+* F) (hσ : σ ≠ RingEquiv.refl F)
    (hsemi : ∀ c v, a (c • v) = σ c • a v) :
    Nat.card F < Nat.card (a - AddMonoidHom.id _).range := by
  have hs : Function.Involutive σ := by
    intro c
    have h : σ (σ c) • (Pi.single 0 1 : Fin 3 → F) = c • Pi.single 0 1 := by
      have hh := ha (c • (Pi.single 0 1 : Fin 3 → F))
      rw [hsemi, hsemi, ha] at hh
      exact hh
    simpa using congrFun h 0
  let δ := a - AddMonoidHom.id (Fin 3 → F)
  have hk : δ.ker = a.eqLocus (AddMonoidHom.id _) := by
    ext v
    change a v - v = 0 ↔ a v = v
    exact sub_eq_zero
  have he := Representation.SemilinearInvolution.fixed_card_sq σ hs hσ a ha hsemi
  rw [← hk] at he
  have hc := δ.ker.card_mul_index
  rw [AddSubgroup.index_ker] at hc
  have hp : 0 < Nat.card δ.ker := Nat.card_pos
  have hr : Nat.card δ.range = Nat.card δ.ker := by nlinarith
  have hsquare : Nat.card δ.range ^ 2 = Nat.card F ^ 3 := by
    rw [hr, he, Nat.card_fun, Nat.card_fin]
  have hF : 1 < Nat.card F := by
    let := Fintype.ofFinite F
    simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card (α := F))
  change Nat.card F < Nat.card δ.range
  by_contra! hh
  have hh' : Nat.card δ.range ^ 2 ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hh 2
  have hq : Nat.card F ^ 2 < Nat.card F ^ 3 := by
    exact Nat.pow_lt_pow_right hF (by decide)
  omega

/-- A semilinear involution with at most q displacements is field-linear.
The same bound treats q=4 and larger binary fields. -/
theorem linear_of_small_displacement (a : (Fin 3 → F) →+ (Fin 3 → F))
    (ha : Function.Involutive a)
    (hsemi : ∃ σ : F ≃+* F, ∀ c v, a (c • v) = σ c • a v)
    (hcard : Nat.card (a - AddMonoidHom.id _).range ≤ Nat.card F) :
    ∀ (c : F) v, a (c • v) = c • a v := by
  obtain ⟨σ, hσ⟩ := hsemi
  have hs : σ = RingEquiv.refl F := by
    by_contra hn
    exact (not_lt_of_ge hcard) (semilinear_displacement_large a ha σ hn hσ)
  simpa only [hs, RingEquiv.refl_apply] using hσ
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear
