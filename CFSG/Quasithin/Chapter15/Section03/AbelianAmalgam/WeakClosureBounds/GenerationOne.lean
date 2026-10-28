module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.Terminal
public import CFSG.Quasithin.ChapterE.Section01.Basic

/-!
# The generation minimum and terminal reduction for 15.3.65(1)

Membership in the actual outside family forces even order, since its two-core
is nontrivial. With a positive E-generation bound, the natural-number minimum
is therefore positive and attained. In particular the zero value of the
infimum of an empty set cannot be used in the generation-one argument.

The imported module proves the final coprime-action contradiction from seed
fixation. E.2.2 Borel recognition, the torus embeddings, and the F.9.18/B.4/B.5
representation calculation are still required before 15.3.65(1) is established.
No theorem in this module is asserted to be the completed source lemma.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
E.1.5–7, printed pp.210–211, and 15.3.65, printed pp.1151–1152.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
open Subgroup ChapterE
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Even order follows from the genuine nontrivial-core condition in H(T,M). -/
theorem two_dvd_card_of_mem_outside
    {T : Sylow 2 G} {M H : Subgroup G} (hH : H ∈ sylowOutsideFamily T M) :
    2 ∣ Nat.card H := by
  have hQ : H.pCoreIn 2 ≠ ⊥ := hH.1.1
  rcases (isPGroup_pCoreIn 2 H).card_eq_or_dvd with hcard | hcard
  · exact False.elim (hQ (card_eq_one.mp hcard))
  · exact hcard.trans (card_dvd_of_le (pCoreIn_le 2 H))

/-- The minimum specification requires an actual positive E-generation bound.
Its existence is the earlier E.1.7 obligation. -/
theorem generation_minimum_spec_of_mem_outside
    {T : Sylow 2 G} {M H : Subgroup G} (hH : H ∈ sylowOutsideFamily T M)
    (hex : ∃ i : ℕ, 0 < i ∧ IsEGenerated i H) :
    0 < generationParameter H ∧ IsEGenerated (generationParameter H) H :=
  generationParameter_spec
    (fun ho => ho.not_two_dvd_nat (two_dvd_card_of_mem_outside hH)) hex

/-- The legitimate numerical case split, including the nonempty minimizing family. -/
theorem generation_eq_one_or_one_lt
    {T : Sylow 2 G} {M H : Subgroup G} (hH : H ∈ minimalSylowOutsideFamily T M)
    (hex : ∃ i : ℕ, 0 < i ∧ IsEGenerated i H) :
    generationParameter H = 1 ∨ 1 < generationParameter H := by
  have hp := (generation_minimum_spec_of_mem_outside hH.prop hex).1
  omega

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne
