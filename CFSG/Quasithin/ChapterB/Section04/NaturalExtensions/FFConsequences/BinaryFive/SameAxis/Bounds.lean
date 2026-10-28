module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Bounds
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.SameAxis.Geometry

/-!
# The hyperplane branch and bounds in the same-orientation case

A faithful nonidentity actor fixing a hyperplane has that hyperplane as its
entire fixed space. Thus any elementary subgroup of rank at least two fixing
a hyperplane contains a literal axis four-group. On two isomorphic natural
factors the offender budget doubles the common fixed codimension. This
settles actor ranks two and three, and restricts the no-axis case to ranks
four through six and factor costs two or three.

Source: Aschbacher–Smith, B.4.9, final paragraph on printed p.95,
combined manuscript of 1 March 2004.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
  [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
/-- Equivalence of the actual factors identifies their fixed codimensions. -/
theorem factor_costs_eq (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    (A : Subgroup G) :
    fixedCodim d.space.quotientRepresentation A = fixedCodim d.space.toRepresentation A := by
  simpa only [Subgroup.map_id] using
    fixedCodim_map_equivariant d.space.quotientRepresentation d.space.toRepresentation
      (MonoidHom.id G) e.toLinearEquiv
      (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A

include hF in
/-- A hyperplane fixed by a noncyclic elementary actor supplies the actual
common axis for all three nonidentity elements of a four-subgroup. -/
theorem axisFour_subgroup_of_cost_one {A : Subgroup G} (hA : IsElementaryTwo A)
    (hr : 2 ≤ rank A) (hm : fixedCodim d.space.quotientRepresentation A = 1) :
    ∃ E : Subgroup G, E ≤ A ∧ QuadraticSplitting.IsAxisFour d E := by
  let : Finite G := Finite.of_injective (BinaryFive.groupEquiv d hF)
    (BinaryFive.groupEquiv d hF).injective
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    Nat.prime_two (IsElementaryAbelian.isPGroup 2 A) (show 2 ^ 2 ≤ Nat.card A by
      rw [hA.card_eq_two_pow_rank]
      exact Nat.pow_le_pow_right (by decide) hr)
  let D := E.map A.subtype
  have hD : D ≤ A := Subgroup.map_subtype_le E
  have hcard : Nat.card D = 4 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hE]
    norm_num
  let : IsElementaryAbelian 2 E := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) x.val }
  refine ⟨D, hD, IsElementaryAbelian.map A.subtype, hcard,
    fixedSpace d.space.quotientRepresentation A, ?_, ?_⟩
  · exact hm.trans hF.symm
  · intro a ha hne
    have hle : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr (hD ha)
    have hfix := fixedSpace_antitone d.space.quotientRepresentation hle
    have hp := fixedCodim_pos_of_faithful d.space.quotientRepresentation
      d.quotient_faithful (show Subgroup.zpowers a ≠ ⊥ by
        intro hz
        exact hne (Subgroup.mem_bot.mp (hz ▸ Subgroup.mem_zpowers a)))
    apply (Submodule.eq_of_le_of_finrank_eq hfix ?_).symm
    have h1 := fixedCodim_add_finrank d.space.quotientRepresentation A
    have h2 := fixedCodim_add_finrank d.space.quotientRepresentation (Subgroup.zpowers a)
    have h3 := Submodule.finrank_mono hfix
    omega


/-- The source budget in the same orientation, before splitting. -/
theorem twice_factor_cost_le_rank
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    {A : Subgroup G} (hA : IsOffender ρ A) :
    2 * fixedCodim d.space.quotientRepresentation A ≤ rank A := by
  have hb := d.offender_budget hA
  rw [← factor_costs_eq d e] at hb
  omega

include hF in
/-- A quadratic offender fixing a quotient hyperplane supplies the full
four-group hypothesis of B.4.9(1). -/
theorem axisFour_of_cost_one {A : Subgroup G} (hA : IsOffender ρ A)
    (hq : IsQuadratic ρ A) (hm : fixedCodim d.space.quotientRepresentation A = 1) :
    HasQuadraticAxisFour d := by
  obtain ⟨E, hEA, hE⟩ := axisFour_subgroup_of_cost_one d hF hA.1
    (d.offender_rank_ge_two hA) hm
  exact ⟨E, hE, fun a ha b hb v => hq a (hEA ha) b (hEA hb) v⟩

include hF in
/-- This completes the same-orientation four-group construction at actor
ranks at most three, with no geometric premise. -/
theorem axisFour_of_rank_le_three
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    {A : Subgroup G} (hA : IsOffender ρ A) (hq : IsQuadratic ρ A)
    (hr : rank A ≤ 3) : HasQuadraticAxisFour d := by
  have hp := (d.factor_costs_pos hA.1.1).2
  have hb := twice_factor_cost_le_rank d e hA
  exact axisFour_of_cost_one d hF hA hq (by omega)

include hF in
/-- The precise bounds used by the remaining geometric placement argument.
The absence hypothesis concerns four-groups inside A, not ambient ones. -/
theorem bounds_of_no_axisFour
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    {A : Subgroup G} (hA : IsOffender ρ A)
    (hno : ¬ ∃ E : Subgroup G, E ≤ A ∧ QuadraticSplitting.IsAxisFour d E) :
    4 ≤ rank A ∧ rank A ≤ 6 ∧
      2 ≤ fixedCodim d.space.quotientRepresentation A ∧
      fixedCodim d.space.quotientRepresentation A ≤ 3 := by
  have hr := rank_le_six d hF hA.1
  have hp := (d.factor_costs_pos hA.1.1).2
  have hb := twice_factor_cost_le_rank d e hA
  have hn : fixedCodim d.space.quotientRepresentation A ≠ 1 := by
    intro hm
    exact hno (axisFour_subgroup_of_cost_one d hF hA.1 (d.offender_rank_ge_two hA) hm)
  omega

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
