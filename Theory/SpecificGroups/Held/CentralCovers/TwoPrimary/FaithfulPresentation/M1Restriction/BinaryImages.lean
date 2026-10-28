module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryContracts
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.SourceRelations
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBound
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.LowerBound
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# Bounding the marked M₁ image in a covering group

Let `h : Presentation → E` be surjective and let `f : E → He` satisfy the
literal triangle `f ∘ h = presentationMap`. If the twelve marked relations
vanish after applying `h`, the local presentation bounds `h(M₁)` by 1,958,400.
Its image under `f` is the original concrete M₁, whose checked lower bound
is the same number. Thus `f` is injective on `h(M₁)`. The checked 2,058-coset
cover places the full kernel inside this subgroup, proving injectivity of `f`.

This works without finiteness or faithfulness of the original presentation.
The double-cover application in `BinaryAssembly` consequently needs only
word identities in its finite covering group, rather than identities in
an independently faithful presentation.

Sources: John Bray's `Held/Model/Source/HeG1-P1.M`; the marked local
presentation and checked upper/lower bounds in `M1Restriction`.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
open Subgroup.CosetWordCertificate
universe u

private theorem map_eval {E : Type u} [Group E] (h : Presentation →* E)
    (w : Word (Fin 3)) :
    h (eval liftedGenerator w) = eval (h ∘ liftedGenerator) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [eval_cons, map_mul, ih, Function.comp_apply]
    cases a.2 <;> simp

/-- Entry 5 is a conjugate of entry 4, also in every homomorphic image. -/
theorem image_five_of_four {E : Type u} [Group E] (h : Presentation →* E)
    (hfour : h (eval liftedGenerator (relationLetters 4)) = 1) :
    h (eval liftedGenerator (relationLetters 5)) = 1 := by
  have he : eval liftedGenerator (relationLetters 5) =
      y ^ 2 * eval liftedGenerator (relationLetters 4) * (y ^ 2)⁻¹ := by
    simp only [relationLetters, relationIndices, List.map_cons, List.map_nil,
      eval_cons, eval_nil, ↓reduceIte, liftedGenerator]
    group
  rw [he, map_mul, map_mul, map_inv, hfour, mul_one, mul_inv_cancel]

/-- The two word families discharge all twelve local relations. -/
theorem imageRelations_of_even_odd {E : Type u} [Group E] (h : Presentation →* E)
    (heven : EvenImageRelations h) (hodd : OddImageRelations h) : ImageRelations h := by
  intro i
  by_cases hi : i.val < 4
  · rw [initial_relations i hi, map_one]
  have hfour := heven 4 (Or.inl rfl)
  fin_cases i
  all_goals first
    | exact False.elim (hi (by decide))
    | exact hfour
    | exact image_five_of_four h hfour
    | exact heven _ (by decide)
    | exact hodd _ (by decide)

private def imageLocalHom {E : Type u} [Group E] (h : Presentation →* E)
    (hrel : ImageRelations h) : LocalPresentation →* E :=
  PresentedGroup.toGroup (f := h ∘ liftedGenerator) (by
    rintro _ ⟨i, rfl⟩
    exact (map_eval h (relationLetters i)).symm.trans (hrel i))

private theorem imageLocalHom_range {E : Type u} [Group E] (h : Presentation →* E)
    (hrel : ImageRelations h) : (imageLocalHom h hrel).range = m1.map h := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    (Set.range localRelator), MonoidHom.map_closure, ← Set.range_comp,
    m1_eq_closure_range, MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext i
  exact PresentedGroup.toGroup.of _

/-- The checked local presentation bounds the image of M₁. -/
theorem image_m1_bound {E : Type u} [Group E] (h : Presentation →* E)
    (hrel : ImageRelations h) :
    Finite (m1.map h) ∧ Nat.card (m1.map h) ≤ 1958400 := by
  have hb := localPresentation_bound
  let := hb.1
  let g := imageLocalHom h hrel
  have hf : Finite g.range := Finite.of_surjective _ g.rangeRestrict_surjective
  have hc : Nat.card g.range ≤ 1958400 :=
    (Nat.card_le_card_of_surjective _ g.rangeRestrict_surjective).trans hb.2
  have hr : g.range = m1.map h := imageLocalHom_range h hrel
  exact hr ▸ ⟨hf, hc⟩

/-- Local image relations and the literal triangle force the covering map
to be injective. No faithfulness of the source presentation is assumed. -/
theorem map_injective_of_imageRelations {E : Type u} [Group E]
    (h : Presentation →* E) (hsurj : Function.Surjective h) (f : E →* He)
    (htriangle : f.comp h = presentationMap) (hrel : ImageRelations h) :
    Function.Injective f := by
  obtain ⟨hfinite, hbound⟩ := image_m1_bound h hrel
  let := hfinite
  let g := f.comp (m1.map h).subtype
  have hr : g.range = concreteSubgroup := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_map, htriangle]
    rw [← m1Map_range]
    have he : m1Map = presentationMap.comp m1.subtype := by
      apply MonoidHom.ext
      intro s
      exact m1Map_apply s
    rw [he, MonoidHom.range_comp, Subgroup.range_subtype]
  have hc : Nat.card (m1.map h) ≤ Nat.card g.range := by
    rw [hr]
    exact hbound.trans concrete_lower_bound
  have hi : Function.Injective g := by
    have hh := (g.rangeRestrict_surjective.bijective_of_nat_card_le hc).1
    intro s t hst
    exact hh (Subtype.ext hst)
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro e he
  obtain ⟨p, rfl⟩ := hsurj e
  have hp : p ∈ presentationMap.ker := by
    change presentationMap p = 1
    rw [← htriangle]
    exact he
  have hm := presentationMap_ker_le_m1_of_cosetCover M1Cosets.cosetCover hp
  have hh : h p ∈ m1.map h := Subgroup.mem_map_of_mem h hm
  have heq : g ⟨h p, hh⟩ = g 1 := by
    change f (h p) = f 1
    rw [map_one]
    exact he
  exact congrArg Subtype.val (hi heq)

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
