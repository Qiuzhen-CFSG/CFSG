module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.FixedPointSetup
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22
public import Theory.GroupAction.PermutationImageComparison
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageData.Points

/-!
# Comparing the Fi23 fixed-point action with the exact Fi22 carrier

After relabeling the fixed letters as one fixed point and 3510 Fi22 letters,
containment for the whole centralizer and lifts of the two exact ATLAS Fi22
generators give the desired image equivalence. These are separate concrete
certificate obligations. This conditional assembly does not assert them or
assert the order of the chosen Fi23 word.

Source: GLS3, Table 5.3u and the Fischer paragraph around line 1042 of
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, which specifies the centralizer `2Fi22`.
The original permutations and action convention are in `AtlasCarriers/source/`.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi23.CentralizerSection
open Theory.GroupAction.PermutationImageComparison
noncomputable def fixedPointImageEquiv_of_relabeling
    (e : FixedLetters ≃ Option (Fin 3510))
    (upper : ∀ g : numerator, ∃ p : Equiv.Perm (Fin 3510), p ∈ Fi22.generated ∧
      ∀ x, e (fixedPointAction g x) = Option.map p (e x))
    (liftA liftB : numerator)
    (ha : ∀ x, e (fixedPointAction liftA x) = Option.map Fi22.generatorA (e x))
    (hb : ∀ x, e (fixedPointAction liftB x) = Option.map Fi22.generatorB (e x)) :
    fixedPointAction.range ≃* Fi22.Carrier := by
  apply rangeEquivClosurePair fixedPointAction (withFixedPoint e)
    (withFixedPoint_injective e) Fi22.generatorA Fi22.generatorB
  · intro g
    obtain ⟨p, hp, he⟩ := upper g
    exact ⟨p, hp, ((eq_withFixedPoint_iff e _ _).mpr he).symm⟩
  · exact ⟨liftA, (eq_withFixedPoint_iff e _ _).mpr ha⟩
  · exact ⟨liftB, (eq_withFixedPoint_iff e _ _).mpr hb⟩

/-- Turn the certified letter table into coordinates on precisely the candidate's
fixed letters. Certifying that fixed set is a separate concrete obligation. -/
noncomputable def fixedPointRelabeling
    (hfixed : ∀ x : Fin 31671,
      inclusion candidate x = x ↔ x ∈ Set.range ImageData.point) :
    FixedLetters ≃ Option (Fin 3510) :=
  (Equiv.ofBijective
    (fun i : Option (Fin 3510) =>
      (⟨ImageData.point i, (hfixed _).mpr ⟨i, rfl⟩⟩ : FixedLetters))
    ⟨fun i j hij => ImageData.point_injective (congrArg Subtype.val hij), by
      intro x
      obtain ⟨i, hi⟩ := (hfixed x.val).mp x.property
      exact ⟨i, Subtype.ext hi⟩⟩).symm

@[simp] theorem fixedPointRelabeling_symm_val
    (hfixed : ∀ x : Fin 31671,
      inclusion candidate x = x ↔ x ∈ Set.range ImageData.point)
    (i : Option (Fin 3510)) :
    ((fixedPointRelabeling hfixed).symm i).val = ImageData.point i := rfl

theorem point_fixedPointRelabeling
    (hfixed : ∀ x : Fin 31671,
      inclusion candidate x = x ↔ x ∈ Set.range ImageData.point)
    (x : FixedLetters) : ImageData.point (fixedPointRelabeling hfixed x) = x.val :=
  congrArg Subtype.val ((fixedPointRelabeling hfixed).symm_apply_apply x)

/-- Pointwise checks on the named Fi23 letters give the literal restriction
identity, with the original left-action convention. -/
theorem fixedPointRelabeling_action_of_points
    (hfixed : ∀ x : Fin 31671,
      inclusion candidate x = x ↔ x ∈ Set.range ImageData.point)
    (g : numerator) (p : Equiv.Perm (Fin 3510))
    (hp : ∀ i : Option (Fin 3510),
      inclusion g.val (ImageData.point i) = ImageData.point (Option.map p i))
    (x : FixedLetters) :
    fixedPointRelabeling hfixed (fixedPointAction g x) =
      Option.map p (fixedPointRelabeling hfixed x) := by
  apply (fixedPointRelabeling hfixed).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  change inclusion g.val x.val =
    ((fixedPointRelabeling hfixed).symm (Option.map p (fixedPointRelabeling hfixed x))).val
  rw [fixedPointRelabeling_symm_val, ← hp, point_fixedPointRelabeling]

/-- Assemble the exact image comparison from fixed-set coverage, containment
for every centralizer element, and the two certified standard-generator lifts.
No order or centralizer identification is assumed. -/
noncomputable def fixedPointImageEquiv_of_point_certificates
    (hfixed : ∀ x : Fin 31671,
      inclusion candidate x = x ↔ x ∈ Set.range ImageData.point)
    (upper : ∀ g : numerator, ∃ p : Equiv.Perm (Fin 3510), p ∈ Fi22.generated ∧
      ∀ i : Option (Fin 3510),
        inclusion g.val (ImageData.point i) = ImageData.point (Option.map p i))
    (liftA liftB : numerator)
    (ha : ∀ i : Option (Fin 3510),
      inclusion liftA.val (ImageData.point i) =
        ImageData.point (Option.map Fi22.generatorA i))
    (hb : ∀ i : Option (Fin 3510),
      inclusion liftB.val (ImageData.point i) =
        ImageData.point (Option.map Fi22.generatorB i)) :
    fixedPointAction.range ≃* Fi22.Carrier := by
  refine fixedPointImageEquiv_of_relabeling (fixedPointRelabeling hfixed) ?_
    liftA liftB ?_ ?_
  · intro g
    obtain ⟨p, hp, he⟩ := upper g
    exact ⟨p, hp, fixedPointRelabeling_action_of_points hfixed g p he⟩
  · exact fixedPointRelabeling_action_of_points hfixed liftA Fi22.generatorA ha
  · exact fixedPointRelabeling_action_of_points hfixed liftB Fi22.generatorB hb

end Sporadic.Fischer.Fi23.CentralizerSection
