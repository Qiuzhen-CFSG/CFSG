module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Commutators

/-!
# Sizes of individual reciprocal displacements

The forward natural coordinates compute the order of each nonzero individual
commutator as q. These are literal ambient commutators, so conjugating back by
the selected g gives the small-displacement hypothesis on the original chosen
module. This calculation does not assume field linearity of the reciprocal action.

Source: Aschbacher--Smith, 11.3.7(4), refs/quasithin.pdf, printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] {T : Sylow 2 G} {H A : Subgroup G} {F : BinaryField}
namespace NaturalSylowCoordinates
variable {m : ℕ} (n : NaturalSylowCoordinates T H A F m)
include n

/-- The original closure has exponent two, as its actual coordinates show. -/
theorem square_eq_one (w : omegaClosure T H) : w ^ 2 = 1 := by
  apply n.coordinates.injective
  rw [map_pow, map_one, pow_two]
  apply Multiplicative.toAdd.injective
  change (n.coordinates w).toAdd + (n.coordinates w).toAdd = 0
  ext i j
  exact CharTwo.add_self_eq_zero _

/-- A nonfixed vector has a nonzero one-dimensional displacement space. -/
theorem finrank_vectorLine (w : omegaClosure T H)
    (hw : (w : G) ∉ centralizer (A : Set G)) :
    Module.finrank F.Carrier (n.vectorLine w) = 1 := by
  apply finrank_span_singleton
  intro hz
  apply hw
  apply (n.mem_fixed_iff w).mpr
  intro i
  exact congrFun (congrFun hz i) 0

/-- Each nontrivial individual commutator has order exactly q. -/
theorem card_vector_commutator (w : omegaClosure T H)
    (hw : (w : G) ∉ centralizer (A : Set G)) :
    Nat.card (⁅A, zpowers (w : G)⁆ : Subgroup G) = Nat.card F.Carrier := by
  rw [n.commutator_vector_eq_line, Nat.card_congr (n.liftSpaceEquiv (n.vectorLine w))]
  rw [Module.natCard_eq_pow_finrank (K := F.Carrier), n.finrank_vectorLine w hw, pow_one]

omit n in
/-- The individual commutator vanishes exactly for fixed vectors. -/
theorem vector_commutator_ne_bot (w : omegaClosure T H)
    (hw : (w : G) ∉ centralizer (A : Set G)) :
    ⁅A, zpowers (w : G)⁆ ≠ ⊥ := by
  intro he
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at he
  exact hw (he (mem_zpowers (w : G)))

end NaturalSylowCoordinates
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
