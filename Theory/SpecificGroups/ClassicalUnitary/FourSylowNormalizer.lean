module

public import Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer.Rigidity
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer.Kernel
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer.Semilinear

/-!
# Solvability of the additive unitary-four root normalizer

The root action intrinsically determines its two-step fixed-vector flag.
Its induced root-parameter action is a semilinear norm similarity over the
fixed field; nonbinary fixed-field scalars force the norm defect to vanish.
Such similarities are scalar multiples of finite-field automorphisms. The
parameter-action kernel is solvable by its explicit scalar-and-shear form,
so the full additive normalizer is solvable.

This supplies the normalizer input for the automorphisms of a unitary-four
Sylow two-subgroup in Aschbacher--Smith, F.1.11 and F.1.12. The actual Sylow
coordinate and characteristic-subgroup bridge is supplied by FourSylowStructure.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer

variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

omit [CharP F 2] in
private theorem exists_fixed_scalar (hK : 2 < Nat.card (FixedField F σ)) :
    ∃ t : FixedField F σ, t ≠ 0 ∧ t ≠ 1 := by
  let : Fintype (FixedField F σ) := Fintype.ofFinite _
  apply ENat.exists_ne_ne_of_three_le _ 0 1
  rw [ENat.card_eq_coe_fintype_card]
  exact_mod_cast (show 3 ≤ Fintype.card (FixedField F σ) by
    simpa only [Nat.card_eq_fintype_card] using Nat.succ_le_of_lt hK)

/-- Every additive root normalizer induces a scalar field automorphism on the
root parameters. -/
theorem parameterAction_mem_fieldSemilinear (hnt : ∃ u, σ u ≠ u)
    (hK : 2 < Nat.card (FixedField F σ)) (g : rootNormalizer F σ hσ) :
    parameterAction F σ hσ g ∈ fieldSemilinear F := by
  obtain ⟨t,ht0,ht1⟩ := exists_fixed_scalar F σ hK
  obtain ⟨φ,hφ⟩ := semilinear_norm_normal_form F σ hσ
    (parameterEquiv F σ hσ g) (fixedEquiv F σ hσ hnt g) hnt
    (parameter_fixedEquiv_mul F σ hσ hnt g)
    (parameter_norm F σ hσ hnt g t ht0 ht1)
  exact (mem_fieldSemilinear F _).mpr ⟨φ,hφ⟩

/-- The full additive normalizer of the faithful unitary-four root action is
solvable over every finite characteristic-two field with nonbinary fixed field. -/
theorem rootNormalizer_isSolvable (hnt : ∃ u, σ u ≠ u)
    (hK : 2 < Nat.card (FixedField F σ)) :
    Group.IsSolvable (rootNormalizer F σ hσ) := by
  let : Group.IsSolvable (fieldSemilinear F) := fieldSemilinear_isSolvable F
  have hr : (parameterAction F σ hσ).range ≤ fieldSemilinear F := by
    rintro s ⟨g,rfl⟩
    exact parameterAction_mem_fieldSemilinear F σ hσ hnt hK g
  let : Group.IsSolvable (parameterAction F σ hσ).range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hr)
  let : Group.IsSolvable (parameterAction F σ hσ).rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact parameterKernel_isSolvable F σ hσ hnt
  exact Group.isSolvable_of_ker_le_range (parameterAction F σ hσ).rangeRestrict.ker.subtype
    (parameterAction F σ hσ).rangeRestrict (by rw [Subgroup.range_subtype])

end Theory.SpecificGroups.ClassicalUnitary.FourSylowNormalizer
