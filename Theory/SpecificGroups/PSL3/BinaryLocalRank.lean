module
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.Quasithin.LocalRank
public import Theory.GroupTheory.PrimeRankZero
/-!
# Positive local prime rank in binary PSL₃

The torus axis `(a,1)` is injective in the actual projective torus: the
cubic scalar kernel has equal coordinates, so its intersection with this
axis is trivial. A prime dividing the field-unit order therefore occurs
in the projective Borel. Its normal unipotent subgroup is a nontrivial
two-group over a binary field, making the Borel an actual two-local.
This supplies the local-rank contribution required in the component
inspection of Aschbacher–Smith A.3.8, printed pp.45–46.
-/

public section
open Matrix Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3.BinaryLocalRank
open CartanActions CartanActions.BorelQuotient LinearThree
variable (F : Type*) [Field F]

/-- A single split-torus coordinate survives the cubic scalar quotient. -/
noncomputable def unitTorus : Fˣ →* PSL(3,F) :=
  (torusMap F).comp (MonoidHom.inl Fˣ Fˣ)

/-- Scalar projection preserves this literal one-dimensional torus. -/
theorem unitTorus_injective : Function.Injective (unitTorus F) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have h : torusMap F (a,1) = 1 := ha
  exact (torusMap_eq_one_iff F (a,1)).mp h |>.1

variable [Finite F]

/-- The torus axis belongs to the literal projective upper triangular subgroup. -/
theorem unitTorus_le_borel : (unitTorus F).range ≤ borel F := by
  rintro _ ⟨a,rfl⟩
  exact torus_le_borel F ⟨(a,1),rfl⟩

/-- Every divisor of the split-unit order gives positive rank in the
actual projective Borel, including the scalar prime three. -/
theorem borel_rank_pos {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card F - 1) :
    1 ≤ primeRank p (borel F) := by
  have hr : 1 ≤ primeRank p Fˣ := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact fun hz => (PrimeRank.eq_zero_iff_not_dvd_card.mp hz) (by rwa [Nat.card_units])
  let f : Fˣ →* borel F := (unitTorus F).codRestrict _ (fun a => unitTorus_le_borel F ⟨a,rfl⟩)
  exact hr.trans (primeRank_le_of_injective p f (fun _ _ h =>
    unitTorus_injective F (congrArg Subtype.val h)))

/-- The same prime contributes in a genuine two-local normalizer. -/
theorem twoLocal_rank_pos {n p : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    [Fact p.Prime] (hd : p ∣ Nat.card F - 1) :
    1 ≤ twoLocalPrimeRank p PSL(3,F) := by
  have hU : unipotent F ≠ ⊥ := by
    intro h
    have hc := card_unipotent F
    rw [h,card_bot] at hc
    have hgt : 1 < Nat.card F := Finite.one_lt_card
    have hh : 1 < Nat.card F ^ 3 := one_lt_pow₀ hgt (by decide : 3 ≠ 0)
    omega
  have hb : IsTwoLocal (borel F) :=
    ⟨unipotent F,hU,unipotent_isTwoGroup F hF,(normalizer_unipotent F hn hF).symm⟩
  exact (borel_rank_pos F hd).trans (hb.primeRank_le p)
end Matrix.PSL3.BinaryLocalRank
