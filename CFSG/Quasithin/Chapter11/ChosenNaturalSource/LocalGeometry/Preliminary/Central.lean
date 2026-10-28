module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Cover
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Cohomology

/-!
# The original central-part alternatives in 11.0.3

The actual natural marking turns the fixed-space projection into a central
cover. The dual cohomology calculation kills its kernel in the SL₃ row and
bounds its binary dimension by n in the Sp₄ and G₂ rows. The full-orbit
centralizer identity then gives vanishing on V_M as well. The final alternative
uses only the separately owned fixed-space invariance implication of 3.2.5;
its Thompson premise is supplied here from the original multiple-overgroup
hypothesis. This implication must still be discharged in final assembly.

Source: Aschbacher--Smith, 11.0.3(3), printed p.760, using 3.2.2(4,6),
3.2.5 and I.1.5--6. Full SL₃ and nonsplit central extensions are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The full SL₃ marking makes the original relative centralizer trivial. -/
theorem sl3_centralizer_eq_bot
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  have hk := finrank_ker_le_H1_of_cover (markedProjection D m)
    (markedProjection_isCover D m)
  rw [LinearThree.dual_H1_finrank S.field S.nonbinary, markedProjection_ker] at hk
  apply Subgroup.eq_bot_of_card_eq
  rw [← Nat.card_congr (centralSpaceEquiv D),
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.eq_zero_of_le_zero hk, pow_zero]

/-- Both centralizers in the SL₃ alternative of 11.0.3(3) vanish. -/
theorem sl3_centralizers_eq_bot
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    V ⊓ centralizer (L : Set G) = ⊥ ∧
      componentOrbit V (normalizer (L : Set G)) ⊓ centralizer (L : Set G) = ⊥ :=
  ⟨sl3_centralizer_eq_bot D S m,
    (fullModule_centralizer_eq_bot_iff D S).mpr (sl3_centralizer_eq_bot D S m)⟩

/-- Source 11.0.3(3) in the Sp₄ row: the actual central part has rank at most n. -/
theorem sp4_centralizer_rank_le
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    Representation.BinaryOffender.rank (V ⊓ centralizer (L : Set G)) ≤ S.field.degree := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  apply centralizer_rank_le_of_dual_cohomology D m
  rw [dual_cohomology_eq_derived]
  exact le_of_eq ((SymplecticFourOrthogonalCover.binary_dual_H1_finrank
    (K := S.field.Carrier)).trans (coefficient_finrank_of_card 2 _ S.field.card_eq))

/-- The same bound in the G₂ row keeps the actual six-dimensional natural quotient. -/
theorem g2_centralizer_rank_le
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    Representation.BinaryOffender.rank (V ⊓ centralizer (L : Set G)) ≤ S.field.degree := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Atlas.G2.Model S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  apply centralizer_rank_le_of_dual_cohomology D m
  rw [dual_cohomology_eq_derived]
  exact le_of_eq ((Atlas.G2.Natural.OrthogonalCover.binary_dual_H1_finrank S.field.Carrier).trans
    (coefficient_finrank_of_card 2 _ S.field.card_eq))

/-- The central-part dichotomy with only the preceding 3.2.5 invariance input.
Its actual Thompson hypothesis is proved, and no cohomology callback remains. -/
theorem central_alternatives_of_fixedSpace_invariance
    (hi : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ →
      V ⊓ centralizer (L : Set G) ≠ ⊥ →
      componentOrbit V (normalizer (L : Set G)) = V) :
    (V ⊓ centralizer (L : Set G) = ⊥ ∧
      componentOrbit V (normalizer (L : Set G)) ⊓ centralizer (L : Set G) = ⊥) ∨
    ((Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))) ∧
      V = componentOrbit V (normalizer (L : Set G)) ∧
      Representation.BinaryOffender.rank (V ⊓ centralizer (L : Set G)) ≤ S.field.degree ∧
      L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆) := by
  by_cases hc : V ⊓ centralizer (L : Set G) = ⊥
  · exact Or.inl ⟨hc, (fullModule_centralizer_eq_bot_iff D S).mpr hc⟩
  · have hJ := thompson_commutator_of_centralizer_ne_bot D S hc
    have hV := (hi hJ hc).symm
    cases S.natural with
    | sl3 hm => exact (hc (sl3_centralizer_eq_bot D S hm.some)).elim
    | sp4 hm => exact Or.inr ⟨Or.inl hm, hV, sp4_centralizer_rank_le D S hm.some, hJ⟩
    | g2 hm => exact Or.inr ⟨Or.inr hm, hV, g2_centralizer_rank_le D S hm.some, hJ⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
