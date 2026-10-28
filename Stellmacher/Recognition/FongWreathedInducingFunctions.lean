module

public import BenderGlauberman.ClassFunction
public import Theory.Character.CyclotomicModels

/-!
# The two inducing functions in Fong's wreathed calculation

For genuine linear homomorphisms alpha and beta, construct the two virtual
characters and their inductions. Writing each as a difference of sums of
linear characters proves generalized-character status. The induced models
come from the monomial representation construction. Both functions and their
inductions vanish on elements of square one. The cubic formula printed in
Fong agrees with the conjugate formula when alpha has exponent four.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), 65–76, printed p. 72.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Stellmacher.Recognition.FongWreathedInduction
attribute [local instance] Fintype.ofFinite
variable {H : Type*} [Group H]

def thetaOne (α β : H →* ℂ) : ClassFunction H :=
  ((1 : H → ℂ) + (β : H → ℂ)) -
    ((α ^ 2 : H →* ℂ) + (α ^ 2 * β : H →* ℂ) : H → ℂ)

def thetaTwo (α β : H →* ℂ) : ClassFunction H :=
  ((α : H → ℂ) + (α * β : H →* ℂ)) -
    ((α ^ 3 : H →* ℂ) + (α ^ 3 * β : H →* ℂ) : H → ℂ)

theorem thetaOne_apply (α β : H →* ℂ) (h : H) :
    thetaOne α β h = (1 - α h ^ 2) * (1 + β h) := by
  simp only [thetaOne, Pi.sub_apply, Pi.add_apply, Pi.one_apply,
    MonoidHom.mul_apply, MonoidHom.pow_apply]
  ring

theorem thetaTwo_apply (α β : H →* ℂ) (h : H) :
    thetaTwo α β h = (α h - α h ^ 3) * (1 + β h) := by
  simp only [thetaTwo, Pi.sub_apply, Pi.add_apply,
    MonoidHom.mul_apply, MonoidHom.pow_apply]
  ring

variable [Finite H]
private theorem hom_isCharacter (α : H →* ℂ) : IsCharacter (α : H → ℂ) := by
  exact BenderGlauberman.isCharacter_of_isIrreducibleCharacter
    (BenderGlauberman.isLinearCharacter_of_hom α.toHomUnits).1

theorem thetaOne_generalized (α β : H →* ℂ) : IsGeneralizedCharacter (thetaOne α β) := by
  refine ⟨_, _, BenderGlauberman.isCharacter_add (hom_isCharacter 1) (hom_isCharacter β),
    BenderGlauberman.isCharacter_add (hom_isCharacter (α ^ 2)) (hom_isCharacter (α ^ 2 * β)), rfl⟩

theorem thetaTwo_generalized (α β : H →* ℂ) : IsGeneralizedCharacter (thetaTwo α β) := by
  refine ⟨_, _, BenderGlauberman.isCharacter_add (hom_isCharacter α) (hom_isCharacter (α * β)),
    BenderGlauberman.isCharacter_add (hom_isCharacter (α ^ 3)) (hom_isCharacter (α ^ 3 * β)), rfl⟩

theorem thetaTwo_conj_formula (α β : H →* ℂ) (hfour : ∀ h, α h ^ 4 = 1) (h : H) :
    thetaTwo α β h = (α h - star (α h)) * (1 + β h) := by
  rw [thetaTwo_apply]
  have hlin : IsLinearCharacter (α : H → ℂ) :=
    BenderGlauberman.isLinearCharacter_of_hom α.toHomUnits
  have hstar := BenderGlauberman.linearChar_star hlin h
  have hinv : α h⁻¹ = α h ^ 3 := by
    apply mul_left_cancel₀ (show α h ≠ 0 from BenderGlauberman.linearChar_ne_zero hlin h)
    rw [← map_mul, mul_inv_cancel, map_one]
    simpa only [← pow_succ'] using (hfour h).symm
  rw [hstar, hinv]

variable {G : Type*} [Group G] [Finite G]
private theorem induced_hom_isCharacter (K : Subgroup G) (α : K →* ℂ) :
    IsCharacter (inducedClassFunction K α) := by
  obtain ⟨n, σ, hσ⟩ := Representation.exists_induced_linear_model_of_range
    (RingHom.id ℂ) Function.injective_id K α (fun h => ⟨α h, rfl⟩)
  exact ⟨n, Representation.mapCoefficients (RingHom.id ℂ) σ, funext (fun g => (hσ g).symm)⟩

def inducedOne (K : Subgroup G) (α β : K →* ℂ) : ClassFunction G :=
  inducedClassFunction K (thetaOne α β)

def inducedTwo (K : Subgroup G) (α β : K →* ℂ) : ClassFunction G :=
  inducedClassFunction K (thetaTwo α β)

private theorem induced_four_generalized (K : Subgroup G) (a b c d : K →* ℂ) :
    IsGeneralizedCharacter (inducedClassFunction K
      (((a : K → ℂ) + (b : K → ℂ)) - ((c : K → ℂ) + (d : K → ℂ)))) := by
  refine ⟨inducedClassFunction K a + inducedClassFunction K b,
    inducedClassFunction K c + inducedClassFunction K d,
    BenderGlauberman.isCharacter_add (induced_hom_isCharacter K a) (induced_hom_isCharacter K b),
    BenderGlauberman.isCharacter_add (induced_hom_isCharacter K c) (induced_hom_isCharacter K d), ?_⟩
  exact (inducedClassFunctionIntLinear K).map_sub _ _ |>.trans
    (by rw [show (inducedClassFunctionIntLinear K) ((a : K → ℂ) + (b : K → ℂ)) =
      inducedClassFunction K a + inducedClassFunction K b from inducedClassFunction_add K a b,
      show (inducedClassFunctionIntLinear K) ((c : K → ℂ) + (d : K → ℂ)) =
      inducedClassFunction K c + inducedClassFunction K d from inducedClassFunction_add K c d])

theorem inducedOne_generalized (K : Subgroup G) (α β : K →* ℂ) :
    IsGeneralizedCharacter (inducedOne K α β) :=
  induced_four_generalized K 1 β (α ^ 2) (α ^ 2 * β)

theorem inducedTwo_generalized (K : Subgroup G) (α β : K →* ℂ) :
    IsGeneralizedCharacter (inducedTwo K α β) :=
  induced_four_generalized K α (α * β) (α ^ 3) (α ^ 3 * β)

end Stellmacher.Recognition.FongWreathedInduction

namespace Stellmacher.Recognition.FongWreathedInduction
attribute [local instance] Fintype.ofFinite
variable {H : Type*} [Group H]

theorem thetaOne_eq_zero_of_sq (α β : H →* ℂ) (h : H) (hh : h ^ 2 = 1) :
    thetaOne α β h = 0 := by
  have ha : α h ^ 2 = 1 := by rw [← map_pow, hh, map_one]
  rw [thetaOne_apply, ha, sub_self, zero_mul]

theorem thetaTwo_eq_zero_of_sq (α β : H →* ℂ) (h : H) (hh : h ^ 2 = 1) :
    thetaTwo α β h = 0 := by
  have ha : α h ^ 2 = 1 := by rw [← map_pow, hh, map_one]
  rw [thetaTwo_apply, pow_succ, ha, one_mul, sub_self, zero_mul]

variable {G : Type*} [Group G] [Finite G]
private theorem induced_eq_zero_of_sq (K : Subgroup G) (φ : ClassFunction K)
    (hφ : ∀ h : K, h ^ 2 = 1 → φ h = 0) (g : G) (hg : g ^ 2 = 1) :
    inducedClassFunction K φ g = 0 := by
  classical
  unfold inducedClassFunction
  have hz : ∀ x : G, (if h : x⁻¹ * g * x ∈ K then φ ⟨_, h⟩ else 0) = 0 := by
    intro x
    split
    · apply hφ
      apply Subtype.ext
      change (x⁻¹ * g * x) ^ 2 = 1
      calc
        _ = x⁻¹ * g ^ 2 * x := by simp only [pow_two]; group
        _ = 1 := by rw [hg]; simp
    · rfl
  simp only [hz, Finset.sum_const_zero, mul_zero]

theorem inducedOne_eq_zero_of_sq (K : Subgroup G) (α β : K →* ℂ)
    (g : G) (hg : g ^ 2 = 1) : inducedOne K α β g = 0 :=
  induced_eq_zero_of_sq K _ (thetaOne_eq_zero_of_sq α β) g hg

theorem inducedTwo_eq_zero_of_sq (K : Subgroup G) (α β : K →* ℂ)
    (g : G) (hg : g ^ 2 = 1) : inducedTwo K α β g = 0 :=
  induced_eq_zero_of_sq K _ (thetaTwo_eq_zero_of_sq α β) g hg

@[simp] theorem inducedOne_one (K : Subgroup G) (α β : K →* ℂ) :
    inducedOne K α β 1 = 0 := inducedOne_eq_zero_of_sq K α β 1 (one_pow 2)

@[simp] theorem inducedTwo_one (K : Subgroup G) (α β : K →* ℂ) :
    inducedTwo K α β 1 = 0 := inducedTwo_eq_zero_of_sq K α β 1 (one_pow 2)
end Stellmacher.Recognition.FongWreathedInduction
