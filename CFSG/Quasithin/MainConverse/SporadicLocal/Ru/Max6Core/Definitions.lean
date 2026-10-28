module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer.Generators

/-!
# The concrete abelian seed in Rudvalis max6

Five conjugates of x^5, where x and y are the unchanged ATLAS max6 generators,
provide a normal abelian two-subgroup. The numerical maps below are witnesses;
all identities are checked in Lean on the original degree-4060 carrier.

Source: Aschbacher--Smith, Theorem 0.1.2(5), printed p.4 (also p.482), and
GLS3 Table 5.3r, p.279. The ATLAS words and permutation conventions are attributed
in Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions and
Model.PermutationData. Witness generation is documented in Max6Core/source/.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.RuEven.Max6Core
open Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.CentralizerCertificate

set_option maxRecDepth 30000

@[expose] public def q₀ : Model := first ^ 5
@[expose] public def q₁ : Model := second * q₀ * second⁻¹
@[expose] public def q₂ : Model := first * q₁ * first⁻¹
@[expose] public def q₃ : Model := second * q₁ * second⁻¹
@[expose] public def q₄ : Model := first * q₂ * first⁻¹

@[expose] public def seedGenerator : Fin 5 → Model := ![q₀, q₁, q₂, q₃, q₄]
@[expose] public def seed : Subgroup Model := Subgroup.closure (Set.range seedGenerator)

public theorem seedGenerator_mem (i : Fin 5) : seedGenerator i ∈ seed :=
  Subgroup.subset_closure ⟨i, rfl⟩

public theorem seed_le_max6 : seed ≤ max6 := by
  have h₀ : q₀ ∈ max6 := max6.pow_mem first_mem 5
  have h₁ : q₁ ∈ max6 := max6.mul_mem (max6.mul_mem second_mem h₀) (max6.inv_mem second_mem)
  have h₂ : q₂ ∈ max6 := max6.mul_mem (max6.mul_mem first_mem h₁) (max6.inv_mem first_mem)
  have h₃ : q₃ ∈ max6 := max6.mul_mem (max6.mul_mem second_mem h₁) (max6.inv_mem second_mem)
  have h₄ : q₄ ∈ max6 := max6.mul_mem (max6.mul_mem first_mem h₂) (max6.inv_mem first_mem)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

/-- The same seed, now intrinsic to the unchanged ATLAS subgroup. -/
@[expose] public def normalSeed : Subgroup max6 := seed.subgroupOf max6

/-- Sixty-four explicit elements; the powers are a C4 x C2^4 coordinate list.
No uniqueness or exhaustiveness is part of this definition. -/
@[expose] public def seedWord (t : Fin 64) : Model :=
  q₀ ^ (t.val % 4) * q₁ ^ (t.val / 4 % 2) * q₂ ^ (t.val / 8 % 2) *
    q₃ ^ (t.val / 16 % 2) * q₄ ^ (t.val / 32 % 2)

public theorem seedWord_mem (t : Fin 64) : seedWord t ∈ seed :=
  seed.mul_mem (seed.mul_mem (seed.mul_mem (seed.mul_mem
    (seed.pow_mem (seedGenerator_mem 0) _) (seed.pow_mem (seedGenerator_mem 1) _))
    (seed.pow_mem (seedGenerator_mem 2) _)) (seed.pow_mem (seedGenerator_mem 3) _))
    (seed.pow_mem (seedGenerator_mem 4) _)

end CFSG.Quasithin.MainConverse.SporadicLocal.RuEven.Max6Core
