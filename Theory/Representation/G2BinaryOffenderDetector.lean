module
public import Theory.Representation.G2BinaryFixedSpaceFamily
public import Theory.Representation.G2BinaryModelOffenders
public import Theory.Representation.BinaryOffender.UniformFixedSpace

/-!
# One-element fixed-space detectors for binary G₂ offenders

Every natural offender is a conjugate of the root eight. The same conjugate
of the short-root involution has fixed codimension three, equal to that of
the whole offender, and therefore has exactly the same fixed space.
This is the detector used in the unique-lift step of AS 3.3.28, p.601.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Atlas.G2.Natural.BinaryModelOffenders
local notation "𝔽" => ZMod 2
local notation "ρ" => NaturalOffenders.binaryNatural (F := ZMod 2)

/-- Every actual binary natural offender contains a single element detecting
its entire fixed space. -/
theorem natural_offender_exists_fixed_detector
    (A : Subgroup (Model 𝔽)) (hA : IsOffender ρ A) :
    ∃ a ∈ A, fixedSpace ρ A = fixedSpace ρ (zpowers a) := by
  obtain ⟨g, hg⟩ := NaturalOffenders.natural_offender_conjugate_elementary
    (n := 1) (by norm_num) (by decide) A hA
  let a := MulAut.conj g (rootC (1 : 𝔽))
  have ha : a ∈ A := by
    rw [hg]
    exact mem_map_of_mem _ (NaturalOffenders.rootC_mem_elementary 1)
  refine ⟨a, ha, fixedSpace_eq_of_fixedCodim_eq ρ (zpowers_le.mpr ha) ?_⟩
  have hdim : fixedCodim ρ A = 3 := by
    simpa using NaturalOffenders.natural_offender_fixedCodim
      (n := 1) (by norm_num) (by decide) A hA
  rw [hdim]
  change 3 = fixedCodim ρ
    (zpowers ((MulAut.conj g).toMonoidHom (rootC (1 : 𝔽))))
  rw [← MonoidHom.map_zpowers, fixedCodim_map_conj]
  exact BinaryFixedFamily.short_root_cost.symm

end Atlas.G2.Natural.BinaryModelOffenders
