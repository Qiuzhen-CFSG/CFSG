module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Branches
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Full.Conjugates
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Full.RegularOrbit
public import Theory.Representation.BinaryOffender.NormalizerOffenderDimension

/-!
# Full-support displacement from seven generating conjugates

The root norm gives dimension at least 64. If seven conjugates of every
nonidentity normalizer involution generate over the component, its fixed
codimension is at least ten. Every nontrivial elementary actor contains
such an involution, so the same bound applies to its common fixed space.
This exceeds twice the actor rank whenever that rank is at most four.

The seven-conjugate theorem in `Full.Conjugates` supplies this bound for
every faithful irreducible representation, including outer involutions.
The final theorem therefore proves `FullSupportRemainingActors` without
any additional generation, module-identification or absolute-irreducibility
premise. Cubicity and radical avoidance are not needed for this full-support
estimate.

Source: Aschbacher–Smith K.3.2, printed pp.451,454–455; Guralnick–Malle,
Classification of 2F-modules, II, author manuscript Proposition4.8(3B).
-/

public section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

open Representation Representation.BinaryOffender
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A nontrivial elementary actor moves at least ten dimensions on a module
with full support, provided the actual normalizer has the seven-conjugate bound. -/
theorem full_support_fixedCodim_ge_ten_of_seven_conjugates
    (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (hgen : NormalizerConjugateGenerationBound σ 7)
    {v : V} (h : LocalHighestVector σ Finset.univ v) (hv : v ≠ 0)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) :
    10 ≤ fixedCodim (normalizerRepresentation σ) A := by
  let : Nontrivial Group := ⟨⟨simpleUpper 0, 1, by decide⟩⟩
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have hd := finrank_le_mul_fixedCodim_of_normalizer_involution σ hf hi hgen t ht1 ht2
  have hdim := sixty_four_le_finrank_of_full_support h hv
  have hfix : fixedSpace (normalizerRepresentation σ) A ≤
      fixedSpace (normalizerRepresentation σ) (Subgroup.zpowers t) := by
    intro x hx g
    exact hx ⟨g, (Subgroup.zpowers_le.mpr ht) g.property⟩
  have hr := Submodule.finrank_mono hfix
  have hAc := fixedCodim_add_finrank (normalizerRepresentation σ) A
  have htc := fixedCodim_add_finrank (normalizerRepresentation σ) (Subgroup.zpowers t)
  omega

/-- Apply the regular-orbit and conjugate-generation estimates to the exact
remaining-actor contract used by the initial-adjacent support assembly. -/
theorem full_support_remaining_actors_of_seven_conjugates
    (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (hgen : NormalizerConjugateGenerationBound σ 7) :
    FullSupportRemainingActors σ := by
  intro v hv h A hA _hc hr _hremaining _havoid
  have hd := full_support_fixedCodim_ge_ten_of_seven_conjugates σ hf hi hgen h hv A hA
  omega

/-- Full support excludes every remaining cubic actor of rank at most four
in the literal linear normalizer of a faithful irreducible binary SL₄-module.
This discharges the full-support premise of
`initial_adjacent_displacement_of_support_estimates`. -/
theorem full_support_remaining_actors
    (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) (hi : σ.IsIrreducible) :
    FullSupportRemainingActors σ :=
  full_support_remaining_actors_of_seven_conjugates σ hf hi
    (normalizer_seven_conjugates σ hf hi)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
