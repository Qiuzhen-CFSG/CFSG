module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.Contracts
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.TensorModel
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.Presentation
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.Comparison
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.Normalizer

/-!
# Proper support separation from a marked mixed-tensor comparison

A nonzero intertwiner from an irreducible module into the actual
natural–exterior tensor is injective. It transports the literal root relations,
so the coordinate exclusion in `TensorModel` rules out support {1,2}.
The last theorem applies this to the existing full-normalizer consumer.

`Comparison` supplies the nonzero intertwiner using the proved simplicity
of the tensor seed's cyclic orbit and control of kernel displacements modulo
the universal highest-vector relations. Thus `proper_support_separation`
requires only irreducibility, and `elementary_le_image_of_proper_highest`
discharges support separation in the full-normalizer consumer.
No absolute irreducibility, degree cutoff, or module catalogue is assumed.

Source application: Guralnick–Malle, Classification of 2F-modules II,
author manuscript, Proposition 4.8(3), pp.27–28; Aschbacher–Smith K.3.2,
printed pp.454–455. The remaining displacement estimates are separate from
this proper-support distinction.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
namespace SupportSeparation
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem map_highest {σ : Representation (ZMod 2) Group V}
    (f : IntertwiningMap σ mixedTensor) {J : Finset (Fin 3)} {v : V}
    (h : LocalHighestVector σ J v) : LocalHighestVector mixedTensor J (f v) := by
  constructor
  · intro i j hij
    rw [← f.isIntertwining, h.upper_fixed i j hij]
  · intro i hi
    rw [← f.isIntertwining, h.inactive_fixed i hi]
  · intro i hi
    simpa only [map_add, f.isIntertwining, map_zero] using congrArg f (h.active_relation i hi)

set_option linter.style.haveILetI false in
/-- An actual nonzero comparison from an irreducible module excludes reversed support. -/
theorem highest_reverse_eq_zero_of_nonzero_intertwiner
    (σ : Representation (ZMod 2) Group V) (hi : IsIrreducible σ)
    (f : IntertwiningMap σ mixedTensor) (hf : f ≠ 0)
    {w : V} (hw : LocalHighestVector σ {1, 2} w) : w = 0 := by
  letI : IsIrreducible σ := hi
  apply (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  rw [map_zero]
  exact mixedTensor_reverse_highest_eq_zero (f w) (map_highest f hw)
end SupportSeparation

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The remaining comparison producer suffices for the published support-separation contract. -/
theorem proper_support_separation_of_mixedTensor_comparison
    (σ : Representation (ZMod 2) Group V) (hi : IsIrreducible σ)
    (hcomparison : ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 1} v →
      ∃ f : IntertwiningMap σ SupportSeparation.mixedTensor, f ≠ 0) :
    ProperSupportSeparation σ := by
  intro v hv hJ w hw hK
  obtain ⟨f, hf⟩ := hcomparison v hv hJ
  exact hw (SupportSeparation.highest_reverse_eq_zero_of_nonzero_intertwiner σ hi f hf hK)

/-- Apply the comparison route to the literal full-normalizer actor consumer. -/
theorem elementary_le_image_of_mixedTensor_comparison
    (σ : Representation (ZMod 2) Group V) (hf : Function.Injective σ)
    (hi : IsIrreducible σ)
    (hcomparison : ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 1} v →
      ∃ f : IntertwiningMap σ SupportSeparation.mixedTensor, f ≠ 0)
    {v : V} (hv : v ≠ 0) (h : LocalHighestVector σ {0, 1} v)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) :
    A ≤ (actionImage σ).subgroupOf (linearNormalizer σ) :=
  Proper.elementary_le_image_of_support_separation σ hf hi
    (proper_support_separation_of_mixedTensor_comparison σ hi hcomparison) hv h A hA

open SupportSeparation in
/-- Apply the universal-kernel reduction to the literal support-separation contract. -/
theorem proper_support_separation_of_tensorOrbit_facts
    (hkernel : ∀ x : Free, tensorOrbitMap x = 0 →
      ∀ g : Group, regular g x - x ∈ relations)
    (hsimple : IsIrreducible tensorOrbit.toRepresentation)
    (σ : Representation (ZMod 2) Group V) (hi : IsIrreducible σ) :
    ProperSupportSeparation σ := by
  apply proper_support_separation_of_mixedTensor_comparison σ hi
  intro v hv h
  exact mixedTensor_comparison_of_kernel_displacements hkernel hsimple σ hi hv h

open SupportSeparation in
/-- The same two concrete model facts place the actual elementary normalizer
actor in the component image, as required by `Proper.Normalizer`. -/
theorem elementary_le_image_of_tensorOrbit_facts
    (hkernel : ∀ x : Free, tensorOrbitMap x = 0 →
      ∀ g : Group, regular g x - x ∈ relations)
    (hsimple : IsIrreducible tensorOrbit.toRepresentation)
    (σ : Representation (ZMod 2) Group V) (hf : Function.Injective σ)
    (hi : IsIrreducible σ)
    {v : V} (hv : v ≠ 0) (h : LocalHighestVector σ {0, 1} v)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) :
    A ≤ (actionImage σ).subgroupOf (linearNormalizer σ) :=
  Proper.elementary_le_image_of_support_separation σ hf hi
    (proper_support_separation_of_tensorOrbit_facts hkernel hsimple σ hi) hv h A hA

/-- The two proper adjacent supports cannot coexist in an irreducible binary
SL₄ module. The concrete comparison premises are all discharged. -/
theorem proper_support_separation
    (σ : Representation (ZMod 2) Group V) (hi : IsIrreducible σ) :
    ProperSupportSeparation σ :=
  proper_support_separation_of_mixedTensor_comparison σ hi
    (fun _ hv h => SupportSeparation.mixedTensor_comparison σ hi hv h)

/-- A proper highest vector forces every elementary subgroup of the literal
full linear normalizer into the component image. -/
theorem elementary_le_image_of_proper_highest
    (σ : Representation (ZMod 2) Group V) (hf : Function.Injective σ)
    (hi : IsIrreducible σ)
    {v : V} (hv : v ≠ 0) (h : LocalHighestVector σ {0, 1} v)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) :
    A ≤ (actionImage σ).subgroupOf (linearNormalizer σ) :=
  Proper.elementary_le_image_of_support_separation σ hf hi
    (proper_support_separation σ hi) hv h A hA

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
