module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.ModelMap
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.SchreierLifting
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactData
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactOrder
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality

/-!
# Faithfulness of the original seven-relator max4 presentation

The original seven-relator group is covered by 168 translates of the image of
its raw edge presentation. Checked elimination replay proves that the frozen
eleven-generator presentation surjects onto that edge presentation. A separate
coset certificate bounds its order by 2048. Thus the original presentation has
order at most 168 · 2048 = 344064, and its existing surjection to the literal
max4 of order 344064 is injective.

The original generators and map are preserved throughout. This is an input to
the local cover calculation supporting Aschbacher--Smith I.1.3(1), printed
p.407; it does not assume the multiplier or any covering conclusion.
-/

public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation
open PresentationFaithfulness
open Subgroup.CosetWordCertificate

/-- The compact relations and generation transfer the compact order bound to
the raw edge presentation. All three premises refer to the frozen literal data. -/
theorem raw_bound_of_compact
    (hrel : ∀ r : Fin 159, eval compactImage (compactRelator r) = 1)
    (hgen : Subgroup.closure (Set.range compactImage) = ⊤)
    (hbound : Finite CompactPresentation ∧ Nat.card CompactPresentation ≤ 2048) :
    Finite RawPresentation ∧ Nat.card RawPresentation ≤ 2048 := by
  let f : CompactPresentation →* RawPresentation :=
    PresentedGroup.toGroup (f := compactImage)
      (by rintro _ ⟨r, rfl⟩; exact hrel r)
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩
  let : Finite CompactPresentation := hbound.1
  exact ⟨Finite.of_surjective f hf,
    (Nat.card_le_card_of_surjective f hf).trans hbound.2⟩

/-- The checked 168-representative cover turns the raw bound into faithfulness
of the literal map to the original max4 subgroup. -/
theorem modelMap_injective_of_raw_bound
    (h : Finite RawPresentation ∧ Nat.card RawPresentation ≤ 2048) :
    Function.Injective modelMap := by
  obtain ⟨hf, hb⟩ := presented_bound_of_raw_bound h
  let : Finite Presented := hf
  apply (modelMap_surjective.bijective_of_nat_card_le ?_).1
  simpa only [SylowOvergroups.max4_card] using hb

/-- Assembly interface for the independent compact lifting and order proofs. -/
theorem modelMap_injective_of_compact
    (hrel : ∀ r : Fin 159, eval compactImage (compactRelator r) = 1)
    (hgen : Subgroup.closure (Set.range compactImage) = ⊤)
    (hbound : Finite CompactPresentation ∧ Nat.card CompactPresentation ≤ 2048) :
    Function.Injective modelMap :=
  modelMap_injective_of_raw_bound (raw_bound_of_compact hrel hgen hbound)

/-- The original seven relators present the literal Rudvalis max4 subgroup.
The compact lifting and order certificates discharge every assembly premise. -/
theorem modelMap_injective : Function.Injective modelMap :=
  modelMap_injective_of_compact compactRelator_eval compactImage_generates
    compactPresentation_bound

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation
