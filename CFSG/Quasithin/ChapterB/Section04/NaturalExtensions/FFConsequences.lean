module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import Theory.Representation.BinaryOffender.DualDisplacement
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.RatioFromStrong
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.QuadraticBound

/-!
# The two-factor FF budget in B.4.9

Both actual natural factors are faithful. The additive extension budget and
the multiplicative displacement bound therefore exclude a hyperplane fixed
space in either factor of a natural-by-dual FF-extension. Rank four forces
quadratic action on the original extension by Thompson replacement. Ranks
four and five have action ratio one, before any splitting is assumed.

These are unconditional steps of B.4.9(2), not the complete splitting or
parabolic classification. In particular the statements retain every natural
dimension; no bound n ≤ 5 or strongly-quasithin assumption is imposed.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9, printed pp.92–95, especially (!) and (**) on p.94.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open QuasisimpleSource
namespace DoubleNatural
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F n ρ)

private theorem faithful_of_equiv {W X : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) G W} {τ : Representation (ZMod 2) G X}
    (e : σ.Equiv τ) (hτ : Function.Injective τ) : Function.Injective σ := by
  intro g h he
  apply hτ
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
  exact (LinearMap.congr_fun (e.isIntertwining' g) v).symm.trans
    ((congrArg e (LinearMap.congr_fun he v)).trans
      (LinearMap.congr_fun (e.isIntertwining' h) v))

private theorem fixedCodim_equiv {W X : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) G W} {τ : Representation (ZMod 2) G X}
    (e : σ.Equiv τ) (A : Subgroup G) : fixedCodim σ A = fixedCodim τ A := by
  simpa only [Subgroup.map_id] using fixedCodim_map_equivariant σ τ (MonoidHom.id G)
    e.toLinearEquiv (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A

/-- The marked natural subrepresentation is faithful in the original actors. -/
theorem natural_faithful : Function.Injective d.space.toRepresentation := by
  intro g h he
  apply d.natural.groupEquiv.injective
  apply ChapterK.Linear.Natural.natural_injective F n
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := d.natural.linearEquiv.surjective w
  rw [← d.natural.intertwines, ← d.natural.intertwines]
  exact congrArg d.natural.linearEquiv (LinearMap.congr_fun he v)

/-- Faithfulness also holds on the literal quotient, in both orientations. -/
theorem quotient_faithful : Function.Injective d.space.quotientRepresentation := by
  rcases d.quotient with h | h
  · obtain ⟨e⟩ := h
    exact faithful_of_equiv e d.natural_faithful
  · obtain ⟨e⟩ := h
    exact faithful_of_equiv e (faithful_dual _ d.natural_faithful)

variable [FiniteDimensional (ZMod 2) V]

/-- Neither factor can have zero cost at a nontrivial actor. -/
theorem factor_costs_pos {A : Subgroup G} (hA : A ≠ ⊥) :
    0 < fixedCodim d.space.toRepresentation A ∧
      0 < fixedCodim d.space.quotientRepresentation A :=
  ⟨fixedCodim_pos_of_faithful _ d.natural_faithful hA,
    fixedCodim_pos_of_faithful _ d.quotient_faithful hA⟩

include d in
/-- The lower bound two in the source inequality (!). -/
theorem offender_rank_ge_two {A : Subgroup G} (hA : IsOffender ρ A) : 2 ≤ rank A := by
  have := d.factor_costs_pos hA.1.1
  have := d.offender_budget hA
  omega

variable [Finite G]

/-- Source (**): a natural-by-dual offender cannot fix a hyperplane on either
factor, and has rank at least four. This holds without assuming splitting. -/
theorem dual_offender_bounds
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsOffender ρ A) :
    2 ≤ fixedCodim d.space.toRepresentation A ∧
      2 ≤ fixedCodim d.space.quotientRepresentation A ∧ 4 ≤ rank A := by
  obtain ⟨hp, hq⟩ := d.factor_costs_pos hA.1.1
  have hs := d.offender_budget hA
  have hm := rank_le_fixedCodim_mul_dual _ d.natural_faithful A
  rw [← fixedCodim_equiv e] at hm
  have h1 : 2 ≤ fixedCodim d.space.toRepresentation A := by
    by_contra! hn
    have he : fixedCodim d.space.toRepresentation A = 1 := by omega
    rw [he, one_mul] at hm
    omega
  have h2 : 2 ≤ fixedCodim d.space.quotientRepresentation A := by
    by_contra! hn
    have he : fixedCodim d.space.quotientRepresentation A = 1 := by omega
    rw [he, mul_one] at hm
    omega
  exact ⟨h1, h2, by omega⟩

/-- The rank-four branch has cost two on each factor and cost four upstairs. -/
theorem dual_rank_four_costs
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsOffender ρ A) (hr : rank A = 4) :
    fixedCodim d.space.toRepresentation A = 2 ∧
      fixedCodim d.space.quotientRepresentation A = 2 ∧ fixedCodim ρ A = 4 := by
  have := d.dual_offender_bounds e hA
  have := fixedCodim_quotient_add_subrepresentation_le ρ d.space A
  have := hA.2
  omega

/-- In rank four, Thompson's replacement must be the original actor. Thus
the quadraticity needed for the splitting criterion is a conclusion. -/
theorem dual_rank_four_quadratic
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsBestOffender ρ A) (hr : rank A = 4) : IsQuadratic ρ A := by
  obtain ⟨B, hBA, hB, hquad, _⟩ :=
    (hA.isOffender ρ).exists_quadratic_minimalBestOffender ρ
  have hb := (d.dual_offender_bounds e (hB.1.isOffender ρ)).2.2
  have he : B = A := Subgroup.eq_of_le_of_card_ge hBA (by
    rw [hA.1.card_eq_two_pow_rank, hB.1.1.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  exact he ▸ hquad

/-- In rank five the factor costs are two and three, in either order.
The full extension has cost five, so its action ratio is exactly one. -/
theorem dual_rank_five_costs
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsOffender ρ A) (hr : rank A = 5) :
    ((fixedCodim d.space.toRepresentation A = 2 ∧
        fixedCodim d.space.quotientRepresentation A = 3) ∨
      (fixedCodim d.space.toRepresentation A = 3 ∧
        fixedCodim d.space.quotientRepresentation A = 2)) ∧ fixedCodim ρ A = 5 := by
  have hb := d.dual_offender_bounds e hA
  have hs := fixedCodim_quotient_add_subrepresentation_le ρ d.space A
  have hm := rank_le_fixedCodim_mul_dual _ d.natural_faithful A
  rw [← fixedCodim_equiv e] at hm
  have ha := hA.2
  have hn : ¬ (fixedCodim d.space.toRepresentation A = 2 ∧
      fixedCodim d.space.quotientRepresentation A = 2) := by
    rintro ⟨h1, h2⟩
    rw [hr, h1, h2] at hm
    omega
  omega

/-- Up to actor rank six, strict offending is possible only in rank six,
with total cost five and factor costs two and three. This is the numerical
lower-bound part of B.4.9(2)(iv). -/
theorem dual_strong_costs
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsStrongOffender ρ A) (hr : rank A ≤ 6) :
    rank A = 6 ∧ fixedCodim ρ A = 5 ∧
      ((fixedCodim d.space.toRepresentation A = 2 ∧
          fixedCodim d.space.quotientRepresentation A = 3) ∨
        (fixedCodim d.space.toRepresentation A = 3 ∧
          fixedCodim d.space.quotientRepresentation A = 2)) := by
  have hb := d.dual_offender_bounds e ⟨hA.1, hA.2.le⟩
  have hs := fixedCodim_quotient_add_subrepresentation_le ρ d.space A
  have hm := rank_le_fixedCodim_mul_dual _ d.natural_faithful A
  rw [← fixedCodim_equiv e] at hm
  have ha := hA.2
  have hn : ¬ (fixedCodim d.space.toRepresentation A = 2 ∧
      fixedCodim d.space.quotientRepresentation A = 2) := by
    rintro ⟨h1, h2⟩
    rw [h1, h2] at hm
    omega
  omega

/-- Once the literal elementary-actor rank bound and a strict offender
witness are supplied, replacement determines the global ratio, without a
separate minimum-attainment premise. -/
theorem dual_ratio_of_rank_bound
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (hr : ∀ A : Subgroup G, IsElementaryTwo A → rank A ≤ 6)
    (hff : IsStrongFFModule ρ) : quadraticRatio ρ = 5 / 6 := by
  apply quadraticRatio_eq_of_strong_ratios ρ hff
  intro A hA
  obtain ⟨hk, hc, _⟩ := d.dual_strong_costs e hA (hr A hA.1)
  simp only [actionRatio, hk, hc, Nat.cast_ofNat]

/-- A rank bound below six rules out strict offending in the dual case. -/
theorem dual_ratio_one_of_rank_bound
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    (hr : ∀ A : Subgroup G, IsElementaryTwo A → rank A ≤ 5)
    (hff : IsFFModule ρ) : quadraticRatio ρ = 1 := by
  apply quadraticRatio_eq_one_of_no_strong ρ hff
  intro A hA
  have hl := hr A hA.1
  have he := (d.dual_strong_costs e hA (by omega)).1
  omega

end DoubleNatural
end CFSG.Quasithin.ChapterB.NaturalExtensions
