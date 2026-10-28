module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson.CentralAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson.Offenders

/-!
# Thompson control from the original natural action

The full LT-action on V descends faithfully through the L-fixed space.
The actual marking of this quotient identifies each offender with one of
the SL3, Sp4 or G2 natural rows. B.2.5 then controls the image of every
maximum elementary subgroup of the specified Sylow. Lifting through the
literal conjugation kernel gives J(T) inside L C_T(L/O2(L)), with both
factors chosen in T.

Source: Aschbacher--Smith, B.4.2(2)--(4), printed p.86, and the final
natural-module argument of 11.4.2, printed p.777.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)

def markedCentralActionEquiv (c : LocalGeometry.Coordinates D S.field) :
    ActionEquiv ((centralAction S).comp (originalLayer S).subtype)
      (restrictScalars (k := ZMod 2) c.modelAction) where
  groupEquiv := (layerEquiv S).symm.trans c.groupEquiv
  linearEquiv := (centralEquiv S).trans c.linearEquiv
  intertwines g v := by
    change c.linearEquiv (centralEquiv S (centralAction S g v)) = _
    rw [show centralEquiv S (centralAction S g v) =
      D.centralQuotientAction ((layerEquiv S).symm g) (centralEquiv S v) from
      (centralActionEquiv S).intertwines g v]
    exact c.intertwines _ _

theorem original_offender_le {A : Subgroup (OriginalQuotient S)}
    (hA : IsOffender (originalAction S) A) : A ≤ originalLayer S :=
  coordinate_offender_le (centralAction S) (originalLayer S) S.field
    (LocalGeometry.coordinates D S) S.nonbinary
    (markedCentralActionEquiv S _) (centralAction_faithful S)
    (original_offender_on_central S hA)

theorem original_offenderSubgroup_le :
    offenderSubgroup (originalAction S) ≤ originalLayer S := by
  apply iSup_le
  intro A
  apply iSup_le
  rintro ⟨hA,_⟩
  exact original_offender_le S (hA.isOffender _)

include S

/-- Thompson control with both factors in the original specified Sylow subgroup. -/
theorem thompson_sylow_control : elementaryAbelianMaxJ (T : Subgroup G) ≤
    ((T : Subgroup G) ⊓ L) ⊔ ((T : Subgroup G) ⊓ Closure.coreQuotientCentralizer L) := by
  apply thompson_le_sylow_join_of_image_le S
  exact (ChapterB.InternalThompsonAction.thompson_image_le (H := originalGroup D)
    (T.subtype le_sup_right) (originalModule S)).trans (original_offenderSubgroup_le S)

/-- The original natural-module containment used at the end of 11.4.2. -/
theorem thompson_control : elementaryAbelianMaxJ (T : Subgroup G) ≤
    L ⊔ ((T : Subgroup G) ⊓ Closure.coreQuotientCentralizer L) :=
  (thompson_sylow_control S).trans (sup_le_sup inf_le_right le_rfl)

include S in
/-- Every original Thompson element is a product of a component Sylow
factor and a Sylow factor centralizing the actual component quotient. -/
theorem thompson_factorization {a : G} (ha : a ∈ elementaryAbelianMaxJ (T : Subgroup G)) :
    ∃ l ∈ (T : Subgroup G) ⊓ L,
      ∃ c ∈ (T : Subgroup G) ⊓ Closure.coreQuotientCentralizer L, a = l * c := by
  have h := thompson_sylow_control S ha
  have hn : (T : Subgroup G) ⊓ Closure.coreQuotientCentralizer L ≤
      normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    apply (le_inf (inf_le_left.trans (T : Subgroup G).le_normalizer) ?_).trans
      inf_normalizer_le_normalizer_inf
    exact inf_le_right.trans (map_subtype_le _)
  change a ∈ ((((T : Subgroup G) ⊓ L) ⊔
    ((T : Subgroup G) ⊓ Closure.coreQuotientCentralizer L) : Subgroup G) : Set G) at h
  rw [coe_mul_of_right_le_normalizer_left _ _ hn] at h
  obtain ⟨l,hl,c,hc,he⟩ := h
  exact ⟨l,hl,c,hc,he.symm⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
