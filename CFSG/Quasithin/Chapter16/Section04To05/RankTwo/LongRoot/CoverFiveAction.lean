module

public import Theory.GroupAction.FiveSevenCentralizer
public import Theory.Alternating.Aut
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.OnanImageBounds

/-!
# The covered residual image bound from one five-subgroup

For the actual action on O₂(X)/Φ(O₂(X)), an order-five subgroup with no
nonidentity fixed point has seven-free centralizer when the section has
order 256. If actors fixing X/O₂(X) centralize this subgroup, the second
intrinsic image bound follows. The actual X/O₂(X)≃A₅ identification
also supplies the first bound via the proved Aut(A₅)≃S₅ theorem.

This consumes the literal residualAction, topAction and sectionAction,
and supplies SourceImageBounds and the existing order-21 contradiction.
The cover owner must construct the marked five-subgroup, its fixed points,
section order, quotient identification and centralizer containment from the
genuine covered model.
A full computation of its module endomorphism ring is unnecessary.

Source: Aschbacher–Smith, Lemma16.5.13, printed p.1202.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
variable {G : Type*} [Group G] [Finite G]

/-- The two actual image bounds follow from the quotient bound and the
fixed-point-free five-subgroup on the precise Frattini section. -/
theorem sourceImageBounds_of_fixed_free_five (V X : Subgroup G)
    (hquot : Nat.Coprime 7 (Nat.card (topAction (residualAction V X)).range))
    (hsection : Nat.card (pCore 2 X ⧸ frattini (pCore 2 X)) = 256)
    (A : Subgroup (MulAut (pCore 2 X ⧸ frattini (pCore 2 X))))
    (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A (pCore 2 X ⧸ frattini (pCore 2 X)) = ⊥)
    (hcentral : ((topAction (residualAction V X)).ker.map
      (sectionAction (residualAction V X))) ≤ centralizer (A : Set _)) :
    SourceImageBounds V X := by
  refine ⟨hquot, ?_⟩
  exact (Theory.GroupAction.seven_coprime_centralizer_of_fixed_free_five
    hsection A hA hfixed).coprime_dvd_right (card_dvd_of_le hcentral)

/-- The fixed-free five calculation excludes the actual exceptional image,
without requiring the stronger equality V=Φ(O₂(X)). -/
theorem no_order_twentyOne_image_of_fixed_free_five {V X : Subgroup G}
    (hVQ : V ≤ twoCore X)
    (hquot : Nat.Coprime 7 (Nat.card (topAction (residualAction V X)).range))
    (hsection : Nat.card (pCore 2 X ⧸ frattini (pCore 2 X)) = 256)
    (A : Subgroup (MulAut (pCore 2 X ⧸ frattini (pCore 2 X))))
    (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A (pCore 2 X ⧸ frattini (pCore 2 X)) = ⊥)
    (hcentral : ((topAction (residualAction V X)).ker.map
      (sectionAction (residualAction V X))) ≤ centralizer (A : Set _))
    (hcard : Nat.card (action V X).range = 21) : False := by
  obtain ⟨hq, hm⟩ := sourceImageBounds_of_fixed_free_five V X hquot hsection A hA hfixed hcentral
  exact no_order_twentyOne_image hVQ hq hm hcard
omit [Finite G] in
/-- The actual quotient identification supplies its seven-free action image. -/
theorem seven_coprime_topAction_of_alternating_five (V X : Subgroup G)
    (e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5)) :
    Nat.Coprime 7 (Nat.card (topAction (residualAction V X)).range) := by
  let s : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  have hcard : Nat.card (MulAut (X ⧸ pCore 2 X)) = 120 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      Nat.card_congr s.symm.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  apply (by decide : Nat.Coprime 7 120).coprime_dvd_right
  exact hcard ▸ (topAction (residualAction V X)).range.card_subgroup_dvd_card

/-- Both literal image bounds follow from the actual A₅ quotient and one
fixed-point-free five-subgroup on the Frattini section. -/
theorem sourceImageBounds_of_alternating_five_and_fixed_free_five (V X : Subgroup G)
    (e : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))
    (hsection : Nat.card (pCore 2 X ⧸ frattini (pCore 2 X)) = 256)
    (A : Subgroup (MulAut (pCore 2 X ⧸ frattini (pCore 2 X))))
    (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A (pCore 2 X ⧸ frattini (pCore 2 X)) = ⊥)
    (hcentral : ((topAction (residualAction V X)).ker.map
      (sectionAction (residualAction V X))) ≤ centralizer (A : Set _)) :
    SourceImageBounds V X :=
  sourceImageBounds_of_fixed_free_five V X
    (seven_coprime_topAction_of_alternating_five V X e) hsection A hA hfixed hcentral
end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
