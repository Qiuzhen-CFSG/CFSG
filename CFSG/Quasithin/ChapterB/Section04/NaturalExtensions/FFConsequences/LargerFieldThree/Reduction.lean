module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.FieldBounds
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.FullAxis
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# The SL₃ offender equality case for two natural factors

Thompson replacement and the defining-field displacement bound exclude
the dual quotient. On a quadratic offender both literal factors then have
binary cost f, the actor has rank 2f, and the original extension has cost 2f.
The replacement is the full axis group in the original natural marking.
Strong replacement also gives quadratic ratio one before splitting.

The remaining geometric step extracts the source four-group from this full
axis actor and establishes universal four-group quadraticity over F₄.
These reductions are independent of that step and of the splitting theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(2)(i)–(ii), printed pp.92–94, especially (!) and (*) on p.94.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open QuasisimpleSource ChapterK.Linear.Natural
namespace DoubleNatural
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V} (d : DoubleNatural F 3 ρ)

private theorem equiv_fixedCodim {W X : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) G W} {τ : Representation (ZMod 2) G X}
    (e : σ.Equiv τ) (A : Subgroup G) : fixedCodim σ A = fixedCodim τ A := by
  simpa only [Subgroup.map_id] using fixedCodim_map_equivariant σ τ (MonoidHom.id G)
    e.toLinearEquiv (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A

/-- Restricting scalars multiplies the literal natural-factor cost by f. -/
theorem three_natural_fixedCodim (A : Subgroup G) :
    fixedCodim d.space.toRepresentation A = F.degree *
      Module.finrank F.Carrier ((Fin 3 → F.Carrier) ⧸
        fieldFixedSpace F 3 (A.map d.natural.groupEquiv.toMonoidHom)) := by
  rw [fixedCodim_map_equivariant _ (linearNatural F 3) d.natural.groupEquiv.toMonoidHom d.natural.linearEquiv d.natural.intertwines,
    fixedCodim_eq_field_codim]

private theorem dual_fixedCodim_model (A : Subgroup G) :
    fixedCodim d.space.toRepresentation.dual A =
      fixedCodim (linearNatural F 3).dual (A.map d.natural.groupEquiv.toMonoidHom) := by
  apply fixedCodim_map_equivariant _ _ _ d.natural.linearEquiv.symm.dualMap
  intro g f
  apply LinearMap.ext
  intro w
  change f (d.space.toRepresentation g⁻¹ (d.natural.linearEquiv.symm w)) =
    f (d.natural.linearEquiv.symm (linearNatural F 3 (d.natural.groupEquiv g)⁻¹ w))
  apply congrArg f
  apply d.natural.linearEquiv.injective
  rw [d.natural.intertwines, d.natural.linearEquiv.apply_symm_apply,
    d.natural.linearEquiv.apply_symm_apply, map_inv]

/-- Every nontrivial actor costs at least f on the natural factor. -/
theorem three_natural_cost_ge_degree {A : Subgroup G} (hne : A ≠ ⊥) :
    F.degree ≤ fixedCodim d.space.toRepresentation A := by
  have hne' : A.map d.natural.groupEquiv.toMonoidHom ≠ ⊥ :=
    fun hb => hne ((A.map_eq_bot_iff_of_injective d.natural.groupEquiv.injective).mp hb)
  have hc := (LargerFieldThree.field_dimensions_pos F 3 hne').1
  rw [d.three_natural_fixedCodim]
  exact Nat.le_mul_of_pos_right _ hc

include d in
/-- Quadratic actors on the extension have rank at most 2f. -/
theorem three_quadratic_rank_bound {A : Subgroup G} (hne : A ≠ ⊥)
    (hq : IsQuadratic ρ A) : rank A ≤ 2 * F.degree := by
  have hne' : A.map d.natural.groupEquiv.toMonoidHom ≠ ⊥ :=
    fun hb => hne ((A.map_eq_bot_iff_of_injective d.natural.groupEquiv.injective).mp hb)
  have hq' := quadratic_map_equivariant d.natural.groupEquiv.toMonoidHom d.natural.linearEquiv d.natural.intertwines
    (quadratic_subrepresentation ρ d.space hq)
  have hb := LargerFieldThree.quadratic_three_rank_bound F hne' hq'
  rwa [rank_map_injective _ d.natural.groupEquiv.injective] at hb

variable [FiniteDimensional (ZMod 2) V]

/-- The defining-field displacement bound excludes an opposite-orientation
quadratic offender on the original extension. -/
theorem three_no_dual_quadratic_offender
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsOffender ρ A) (hq : IsQuadratic ρ A) : False := by
  have hne' : A.map d.natural.groupEquiv.toMonoidHom ≠ ⊥ :=
    fun hb => hA.1.1 ((A.map_eq_bot_iff_of_injective d.natural.groupEquiv.injective).mp hb)
  have hq' := quadratic_map_equivariant d.natural.groupEquiv.toMonoidHom d.natural.linearEquiv d.natural.intertwines
    (quadratic_subrepresentation ρ d.space hq)
  have hb := LargerFieldThree.quadratic_three_dual_cost F hne' hq'
  rw [rank_map_injective _ d.natural.groupEquiv.injective,
    ← fixedCodim_map_equivariant _ (linearNatural F 3) d.natural.groupEquiv.toMonoidHom d.natural.linearEquiv d.natural.intertwines,
    ← d.dual_fixedCodim_model, ← equiv_fixedCodim e] at hb
  exact Nat.not_lt_of_ge (d.offender_budget hA) hb

/-- Replacement rules out the dual quotient without assuming splitting. -/
theorem three_same_orientation (hff : IsFFModule ρ) :
    Nonempty (d.space.quotientRepresentation.Equiv d.space.toRepresentation) := by
  rcases d.quotient with h | h
  · exact h
  · obtain ⟨e⟩ := h
    obtain ⟨A, hA⟩ := hff
    let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
    obtain ⟨B, _, hB, hq, _⟩ := hA.exists_quadratic_minimalBestOffender ρ
    exact (d.three_no_dual_quadratic_offender e (hB.1.isOffender ρ) hq).elim

/-- The two-factor budget is saturated on every quadratic offender. -/
theorem three_quadratic_offender_costs {A : Subgroup G}
    (hA : IsOffender ρ A) (hq : IsQuadratic ρ A) :
    rank A = 2 * F.degree ∧ fixedCodim d.space.toRepresentation A = F.degree ∧
      fixedCodim d.space.quotientRepresentation A = F.degree ∧
        fixedCodim ρ A = 2 * F.degree := by
  obtain ⟨e⟩ := d.three_same_orientation ⟨A, hA⟩
  have he := equiv_fixedCodim e A
  have hl := d.three_natural_cost_ge_degree hA.1.1
  have hr := d.three_quadratic_rank_bound hA.1.1 hq
  have hb := d.offender_budget hA
  have hs := fixedCodim_quotient_add_subrepresentation_le ρ d.space A
  have ho := hA.2
  omega

include d in
/-- The quadratic ratio equals one before any complement is constructed. -/
theorem three_ratio (hff : IsFFModule ρ) : quadraticRatio ρ = 1 := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  apply quadraticRatio_eq_one_of_no_strong ρ hff
  intro A hA
  obtain ⟨B, _, hB, hq, hs⟩ := hA.exists_quadratic_minimalBestOffender ρ
  have hc := d.three_quadratic_offender_costs (hB.1.isOffender ρ) hq
  have := hs.2
  omega

/-- Replacement stays inside the supplied actor and realizes the sharp costs. -/
theorem three_quadratic_replacement {A : Subgroup G} (hA : IsBestOffender ρ A) :
    ∃ B ≤ A, IsMinimalBestOffender ρ B ∧ IsQuadratic ρ B ∧
      rank B = 2 * F.degree ∧ fixedCodim d.space.toRepresentation B = F.degree ∧
        fixedCodim d.space.quotientRepresentation B = F.degree ∧
          fixedCodim ρ B = 2 * F.degree := by
  let : Finite G := Finite.of_injective d.natural.groupEquiv d.natural.groupEquiv.injective
  obtain ⟨B, hBA, hB, hq, _⟩ := (hA.isOffender ρ).exists_quadratic_minimalBestOffender ρ
  exact ⟨B, hBA, hB, hq, d.three_quadratic_offender_costs (hB.1.isOffender ρ) hq⟩


/-- The same actor marking presents the literal quotient as a natural module.
Only the vector coordinates use the proved equivariant quotient identification. -/
@[expose] noncomputable def threeQuotientAction
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation) :
    ActionEquiv d.space.quotientRepresentation (linearNatural F 3) where
  groupEquiv := d.natural.groupEquiv
  linearEquiv := e.toLinearEquiv.trans d.natural.linearEquiv
  intertwines g v :=
    (congrArg d.natural.linearEquiv (LinearMap.congr_fun (e.isIntertwining' g) v)).trans
      (d.natural.intertwines g (e v))

omit [FiniteDimensional (ZMod 2) V] in
/-- Quotient coordinates preserve the originally supplied actor marking. -/
@[simp] theorem threeQuotientAction_groupEquiv
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation) :
    (d.threeQuotientAction e).groupEquiv = d.natural.groupEquiv := rfl

/-- The quadratic replacement is an actual full axis subgroup on both factors.
The subgroup is still inside the originally supplied best offender. -/
theorem three_full_axis_replacement {A : Subgroup G} (hA : IsBestOffender ρ A) :
    ∃ (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
      (B : Subgroup G), B ≤ A ∧ IsMinimalBestOffender ρ B ∧ IsQuadratic ρ B ∧
        rank B = 2 * F.degree ∧
        IsFullAxisGroup F 3 (B.map d.natural.groupEquiv.toMonoidHom) ∧
        IsFullAxisGroup F 3 (B.map (d.threeQuotientAction e).groupEquiv.toMonoidHom) := by
  obtain ⟨e⟩ := d.three_same_orientation ⟨A, hA.isOffender ρ⟩
  obtain ⟨B, hBA, hB, hq, hr, hc, _⟩ := d.three_quadratic_replacement hA
  have hm := LargerFieldThree.full_axis_of_rank_cost F
    (elementary_map_injective d.natural.groupEquiv.toMonoidHom d.natural.groupEquiv.injective hB.1.1)
    (by rwa [rank_map_injective _ d.natural.groupEquiv.injective])
    (by rwa [← fixedCodim_map_equivariant _ (linearNatural F 3)
      d.natural.groupEquiv.toMonoidHom d.natural.linearEquiv d.natural.intertwines])
  exact ⟨e, B, hBA, hB, hq, hr, hm, hm⟩

end DoubleNatural
end CFSG.Quasithin.ChapterB.NaturalExtensions
