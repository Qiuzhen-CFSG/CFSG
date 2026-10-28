module
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Displacement
public import Theory.GroupTheory.NormalSectionTwoResidual

public import Theory.GroupTheory.PCoreLocalSetup

/-!
# A single cubic layer determines the whole core commutator

A finite two-perfect group with simple quotient by its two-core has a
normal moved two-subgroup U. If a cubic subgroup moves U and has cubic
length at most one on the whole two-core, equality of fixed-point indices
makes it fix the quotient by U. Normal generation in the simple quotient
then gives [O₂(G),G]=U. No splitting of the two-core is required.

The original reciprocal-component application is Aschbacher–Smith 13.4.15,
printed p.912, implemented in FixedCoreSource/Nonsolvable/ReciprocalCore.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement.CubicComparison
variable {G F : Type*} [Group G] [Finite G] [Group F] [IsSimpleGroup F]

/-- One moved cubic layer exhausts the full two-core budget. -/
theorem core_commutator_eq_of_one_cubic_layer
    (f : G →* F) (hf : Function.Surjective f) (hk : f.ker = pCore 2 G)
    (hp : IsPPerfect 2 G) (U A : Subgroup G) [U.Normal]
    (hUQ : U ≤ pCore 2 G) (hU : ⁅U,(⊤ : Subgroup G)⁆ = U)
    (hA : IsPGroup 3 A) (himage : A.map f ≠ ⊥)
    (hmove : ⁅U,A⁆ ≠ ⊥) (hbound : conjugationCubicLength A (pCore 2 G) ≤ 1) :
    ⁅pCore 2 G,(⊤ : Subgroup G)⁆ = U := by
  have hpos : conjugationCubicLength A U ≠ 0 := by
    intro hz
    have hh := commutator_le_of_length_eq A U ⊥ hA (pCore_isPGroup.to_le hUQ)
      bot_le le_normalizer_of_normal (by rw [normalizer_eq_top]; exact le_top) (by simpa using hz.symm)
    exact hmove (le_bot_iff.mp hh)
  have he : conjugationCubicLength A U = conjugationCubicLength A (pCore 2 G) := by
    have hm := conjugationCubicLength_mono A hUQ
    omega
  have hc := commutator_le_of_length_eq A (pCore 2 G) U hA pCore_isPGroup hUQ
    le_normalizer_of_normal le_normalizer_of_normal he
  have hb := commutator_pResidual_le_of_simple_kernel_escape 2 f hf
    (hk ▸ pCore_isPGroup) (pCore 2 G) U A
    (fun hh => himage ((map_eq_bot_iff A).mpr hh)) hc
  rw [(pResidual_eq_top_iff 2 G).mpr hp] at hb
  exact le_antisymm hb (hU.symm.le.trans (commutator_mono hUQ le_rfl))
end NoncentralChiefRefinement.CubicComparison
