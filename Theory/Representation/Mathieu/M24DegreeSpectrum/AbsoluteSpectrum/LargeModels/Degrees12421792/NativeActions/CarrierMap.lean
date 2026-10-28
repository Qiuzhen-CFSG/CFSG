module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
public import Theory.Mathieu.M24.ValueBoundParabolics.Construction.Generation
import all Theory.Mathieu.M24.ValueBoundParabolics.Construction.Generators

/-!
# The presentation maps onto native M₂₄

The existing three native parabolics generate the full Witt-design group.
Their four Sylow generators and three extra generators are certified positive
words in the two standard permutations. Lifting those words to the abstract
presentation proves that `toCarrier` is surjective.

The internal import above deliberately reuses the private extra-word
certificates; no private data enter the public statements. Injectivity still
requires an abstract finite order bound, combined below with the native order.

Sources: ATLAS `M24G1-P1`; the native generation proof for
Aschbacher–Smith E.4.3(2), printed p.242 (PDF p.253).
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
open Sporadic.Mathieu
open M24LocalGeometry.SylowNormalizer
open M24ValueBoundParabolics.Construction

private theorem standardWord_lift (w : List (Fin 2)) :
    ∃ x : UniversalGroup, (toCarrier x).val = standardWord w := by
  induction w with
  | nil => exact ⟨1, rfl⟩
  | cons c w ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨PresentedGroup.of c * x, ?_⟩
    rw [map_mul]
    change (toCarrier (PresentedGroup.of c)).val * (toCarrier x).val = _
    rw [hx]
    fin_cases c <;> simp [standardWord, standardLetter, a, b]

private theorem sylowGenerator_mem_range (i : Fin 4) :
    generator i ∈ toCarrier.range := by
  obtain ⟨x, hx⟩ := standardWord_lift (generatorWord i)
  exact ⟨x, Subtype.ext (hx.trans (generatorPerm_eq_word i).symm)⟩

private theorem extra_mem_range (i : Fin 3) : extra i ∈ toCarrier.range := by
  obtain ⟨x, hx⟩ := standardWord_lift (extraWord i)
  exact ⟨x, Subtype.ext (hx.trans (extraPerm_eq_word i).symm)⟩

/-- The explicit presentation maps onto the full native group, with its original marking. -/
theorem toCarrier_surjective : Function.Surjective toCarrier := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← parabolic_iSup]
  apply iSup_le
  intro i
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · exact sylowGenerator_mem_range 0
  · exact sylowGenerator_mem_range 1
  · exact sylowGenerator_mem_range 2
  · exact sylowGenerator_mem_range 3
  · exact extra_mem_range i

/-- A finite order bound for the abstract presentation supplies the remaining
carrier comparison. No bound is assumed for a merely named external group. -/
theorem toCarrier_injective_of_bound
    (h : Finite UniversalGroup ∧ Nat.card UniversalGroup ≤ 244823040) :
    Function.Injective toCarrier := by
  let : Finite UniversalGroup := h.1
  apply (toCarrier_surjective.bijective_of_nat_card_le _).1
  rw [m24_order]
  exact h.2

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
