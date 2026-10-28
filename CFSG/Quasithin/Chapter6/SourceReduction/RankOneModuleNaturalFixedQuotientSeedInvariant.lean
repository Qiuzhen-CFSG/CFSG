module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRecognition
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.AlternatingFive
-- The existing seed-source construction and orbit bound are used only to
-- construct the same marked Chapter K input, without changing its public API.
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRecognition

/-!
# Sylow invariance of the original fixed-free chosen constituent

The cubic orbit bound makes a moved chosen constituent an FF-module. Chapter K
then gives either the natural module, which is invariant under every component
automorphism, or the Hermitian module at half-degree one. The latter is the
actual natural A₅ module, with its original component action retained, and its
automorphism invariance also contradicts movement. Thus the chosen constituent
is Sylow invariant in every degree, including degree two.

This is the constituent-invariance step used in source 5.1.3 and 6.1.4. It does
not identify a constituent with the whole reduced module.
Source: Aschbacher–Smith, 5.1.3 and D.3.10, printed pp.630–631 and 197–198.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
open Representation.OrthogonalFourMinus
local instance seedInvariantFixedAlgebra (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) :=
  ZMod.algebra _ 2
local instance seedInvariantBinarySpace (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s) (algebraMap (ZMod 2) (FiniteModel.fixedField s))

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W V : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)

private theorem orthogonal_one_alternating_coordinates
    {E X : Type*} [Group E] [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) E X} {K : Subgroup E}
    (M : ChapterK.RankOne.OrthogonalModel 1 ρ K) :
    Nonempty (ActionEquiv (ρ.comp K.subtype) (alternatingNatural 5)) := by
  let b : X →+ BinaryPermutation.natural (Fin 5) := {
    toFun := fun v => AlternatingFive.moduleEquiv (M.coordinates v)
    map_zero' := by simp
    map_add' := by intros; simp }
  let c : X ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
    LinearEquiv.ofBijective (b.toZModLinearMap 2)
      (AlternatingFive.moduleEquiv.bijective.comp M.coordinates.bijective)
  refine ⟨⟨M.groupEquiv.trans AlternatingFive.groupEquiv, c, ?_⟩⟩
  intro g v
  change AlternatingFive.moduleEquiv (M.coordinates (ρ g.val v)) =
    BinaryPermutation.naturalRepresentation (Fin 5)
      (AlternatingFive.groupEquiv (M.groupEquiv g)).val
        (AlternatingFive.moduleEquiv (M.coordinates v))
  rw [M.intertwines]
  exact AlternatingFive.intertwines (M.groupEquiv g) (M.coordinates v)

include D

/-- The original fixed-free chosen constituent is normalized by the Sylow
subgroup, including in field degree two. -/
theorem rankOne_sylow_normalizes_fixed_free_seed
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    (T : Subgroup G) ≤ normalizer (V : Set G) := by
  by_contra hn
  have hm : V < componentOrbit V (T : Subgroup G) := by
    apply lt_of_le_of_ne (le_componentOrbit V T)
    intro he
    apply hn
    rw [he, ← D.sourceOrbit_eq]
    exact D.sourceOrbit_weakClosure_setup.normalizes
  have hff := D.seed_ff_of_moved h.original_section1221 (D.orbit_bound h) hc hm
  have hs := D.seed_chapterK_of_ff h hc hff
  let a := MulEquiv.ofBijective D.componentQuotientHom
    ⟨quotient_action_injective h _ D.componentQuotientHom_surjective,
      D.componentQuotientHom_surjective⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let ea := a.symm.trans (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm)
  obtain ⟨_, hnat | ⟨s, _, _, hp, _, ⟨M⟩⟩⟩ :=
    hs.binary_recognition ea n (by have := h.exponent; omega) hF
  · obtain ⟨M⟩ := hnat.2
    exact hn (D.sylow_normalizes_of_model_twists h.quotient_quasisimple hc
      (SL2.BinarySmall.natural (K := F)) (Theory.PSL2.sl2_center_eq_bot F)
      ⟨M.groupEquiv, M.coordinates, M.intertwines⟩
      (linear_two_natural_twist (F := F)))
  · let : NeZero s := ⟨hp.ne'⟩
    rcases (hs.orthogonal_case M).2 with hnon | ⟨hs1, _⟩
    · exact hnon.2.2.2 hff
    · have M₁ : ChapterK.RankOne.OrthogonalModel 1 D.seedRepresentation D.componentImage := by
        simpa only [hs1] using M
      apply D.seed_not_alternatingNatural_of_moved h.quotient_quasisimple hc hm
        5 (by decide) (by decide)
      exact orthogonal_one_alternating_coordinates M₁

/-- The source orbit equals the original fixed-free chosen constituent. -/
theorem rankOne_sourceOrbit_eq_of_fixed_free
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) : D.sourceOrbit = V := by
  rw [D.sourceOrbit_eq]
  exact le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl
    (D.rankOne_sylow_normalizes_fixed_free_seed h hc)) (le_componentOrbit V T)

/-- Natural or Hermitian coordinates on the original chosen constituent,
with no degree exception or supplied orbit-invariance premise. -/
theorem rankOne_fixed_free_seed_models
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    IsNaturalModule L V n ∨
      ∃ s : ℕ, n = 2 * s ∧ ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩;
        IsConjugationModel L V (SL2.BinarySmall.hermitian s) := by
  have he := D.rankOne_sourceOrbit_eq_of_fixed_free h hc
  simpa only [he] using D.localCartan_invariant_seed_models h hc he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
