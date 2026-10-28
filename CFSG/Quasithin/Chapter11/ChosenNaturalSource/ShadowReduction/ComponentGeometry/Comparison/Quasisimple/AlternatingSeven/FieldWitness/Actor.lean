module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Natural
public import Theory.SpecificGroups.AlternatingSeven.ConjugatePairs
/-!
# The whole literal action quotient is symmetric seven

The component is the centerless generalized Fitting subgroup. Conjugation
therefore embeds the whole quotient in Aut(A7) = S7. The natural offender
coordinates already have order 5040, so they extend to the whole quotient.
Source: Aschbacher--Smith, 11.4.2, printed p.777; GLS3, 5.2.1.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)
/-- F* has trivial ambient centralizer in the alternating-seven case. -/
theorem componentImage_centralizer_eq_bot
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hmodel : AlternatingSevenModel E) :
    centralizer (componentImage E : Set (ActionQuotient E)) = ⊥ := by
  obtain ⟨e⟩ := hmodel.2
  have hF := (action_structure E h hf hne hstar hcent).2.1
  have hc : centralizer (componentImage E : Set (ActionQuotient E)) ≤ componentImage E := by
    rw [show componentImage E = generalizedFitting (ActionQuotient E) from hF]
    exact centralizer_generalizedFitting_le _
  apply bot_unique
  intro x hx
  let y : componentImage E := ⟨x,hc hx⟩
  have hy : y ∈ center (componentImage E) := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hx k k.property)
  have he : e y ∈ center (alternatingGroup (Fin 7)) := (centerCongr e ⟨y,hy⟩).property
  rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
  exact congrArg Subtype.val (e.injective (he.trans (map_one e).symm))

/-- The natural actor coordinates cover the entire original action quotient. -/
theorem offenderGroup_eq_top
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (hmodel : AlternatingSevenModel E)
    (t : MovedSection (action E) (componentImage E))
    (a : MarkedActionEquiv t.space.toRepresentation (offenderGroup E) (componentImage E)
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) :
    offenderGroup E = ⊤ := by
  let := componentImage_normal E h
  let q := _root_.AlternatingSeven.ConjugatePairs.action (componentImage E) a.subgroupEquiv
  have hq := _root_.AlternatingSeven.ConjugatePairs.action_injective (componentImage E)
    a.subgroupEquiv (componentImage_centralizer_eq_bot E h hf hne hstar hcent hmodel)
  apply (eq_of_le_of_card_ge (show offenderGroup E ≤ ⊤ from le_top) ?_)
  rw [card_top, Nat.card_congr a.action.groupEquiv.toEquiv]
  exact Nat.card_le_card_of_injective q hq

/-- The same seven-letter coordinates, now on every original quotient element. -/
@[expose] def quotientEquiv
    (htop : offenderGroup E = ⊤)
    (t : MovedSection (action E) (componentImage E))
    (a : MarkedActionEquiv t.space.toRepresentation (offenderGroup E) (componentImage E)
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) :
    ActionQuotient E ≃* Equiv.Perm (Fin 7) :=
  (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm).trans a.action.groupEquiv

theorem quotientEquiv_apply (htop : offenderGroup E = ⊤)
    (t : MovedSection (action E) (componentImage E))
    (a : MarkedActionEquiv t.space.toRepresentation (offenderGroup E) (componentImage E)
      (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7)))
    (x : offenderGroup E) : quotientEquiv E htop t a x = a.action.groupEquiv x := rfl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
