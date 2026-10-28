module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Realization
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison.Generators

/-!
# The marked pair generates the full native M24

The native M23 generators are explicit words in this pair. They generate the
whole point stabilizer; primitivity and the point-moving first generator then
give the full Witt-design automorphism group. No presentation is assumed.

Source: the native generator words in `Theory/Mathieu/M23/Generators.lean`;
GM02, Proposition 5.1, uses these native Mathieu carriers.
-/

public noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.LargeInvolutionGeneration
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair
open Subgroup

theorem native_generators_closure :
    closure ({generatorA, generatorB} : Set M24) = ⊤ := by
  let H := closure ({generatorA, generatorB} : Set M24)
  have ha : m24GeneratorAInM24 ∈ H := subset_closure (by simp [generatorA, m24GeneratorAInM24])
  have hb : m24GeneratorBInM24 ∈ H := subset_closure (by simp [generatorB, m24GeneratorBInM24])
  have hc : m23AtlasConjugator ∈ H := H.mul_mem (H.mul_mem (H.mul_mem hb ha) hb) ha
  have hra : m23AtlasRawA ∈ H := by
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hb ha)
      (H.pow_mem (H.mul_mem hb (H.pow_mem (H.mul_mem ha hb) 4)) 4))
      (H.inv_mem ha)) (H.inv_mem hb)
  have hrb : m23AtlasRawB ∈ H := by
    have hx := H.mul_mem (H.mul_mem hb ha) hb
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hb (H.pow_mem hx 2))
      (H.pow_mem (H.mul_mem (H.mul_mem (H.mul_mem hb ha) (H.pow_mem hx 2)) ha) 2))
      (H.inv_mem hb)) (H.pow_mem (H.mul_mem (H.inv_mem ha) (H.pow_mem (H.inv_mem hb) 2)) 2)
  have he : H.comap embedding = ⊤ := by
    apply top_unique
    rw [← Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison.native_generates,
      closure_le]
    rintro x (rfl | rfl)
    · change (m23SimplicityExtendHom m23GeneratorAInM23).val ∈ H
      rw [m23GeneratorA_extension]
      exact H.mul_mem (H.mul_mem hc hra) (H.inv_mem hc)
    · change (m23SimplicityExtendHom m23GeneratorBInM23).val ∈ H
      rw [m23GeneratorB_extension]
      exact H.mul_mem (H.mul_mem hc hrb) (H.inv_mem hc)
  apply m24_eq_top_of_generators
  · change a23 ∈ H.comap embedding
    rw [he]; trivial
  · change b23 ∈ H.comap embedding
    rw [he]; trivial
  · change m23Standard23 ∈ H.comap embedding
    rw [he]; trivial
  · exact ha

theorem native_generators_monoid_closure :
    Submonoid.closure ({generatorA, generatorB} : Set M24) = ⊤ := by
  rw [← Subgroup.closure_toSubmonoid_of_finite, native_generators_closure]
  rfl

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair
