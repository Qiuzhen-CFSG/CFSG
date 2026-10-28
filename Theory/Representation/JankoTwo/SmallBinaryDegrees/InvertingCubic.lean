module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Fusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms.Full

/-!
# Cubic inversion by every Hall--Janko involution

Two explicit words conjugate the literal cubic generator to elements inverted
by the two inner involution representatives. The outer representative already
inverts that generator. Exhaustive inner and outer fusion therefore gives an
inverted automorphic image of the same cubic element for every involutory
automorphism of the actual degree-100 carrier.

The word equalities are checked on the existing permutation tables by Lean's
kernel. Source: the 3B-inversion argument in Guralnick--Malle, Classification
of 2F-modules I, Proposition 5.1, manuscript p.16; the ATLAS J2G1-p100B0
permutations and their attribution are retained in the imported carrier modules.
No representation-theoretic fixed-space calculation is assumed here.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.InvertingCubic
open Sporadic.LeechRelated.J2
open GeneratorPair ExceptionalParabolics

private def firstConjugator : Carrier := b * a * b * a * b⁻¹ * a * b * a * b⁻¹ * a * b * a * b⁻¹ * a * b⁻¹ * a * b * a * b⁻¹ * a * b⁻¹ * a * b * a * b * a
private def secondConjugator : Carrier := b⁻¹ * a * b⁻¹ * a * b * a * b⁻¹ * a * b * a * b⁻¹ * a * b * a * b * a

set_option maxRecDepth 20000 in
private theorem first_inverts :
    a * (firstConjugator * b * firstConjugator⁻¹) * a⁻¹ =
      (firstConjugator * b * firstConjugator⁻¹)⁻¹ := by
  apply inclusion_injective
  simp only [firstConjugator, map_mul, map_inv]
  simp only [show inclusion a = tableA from generatorA_eq_table,
    show inclusion b = tableB from generatorB_eq_table]
  decide +kernel

set_option maxRecDepth 20000 in
private theorem second_inverts :
    FirstFusion.t * (secondConjugator * b * secondConjugator⁻¹) * FirstFusion.t⁻¹ =
      (secondConjugator * b * secondConjugator⁻¹)⁻¹ := by
  apply inclusion_injective
  simp only [secondConjugator, map_mul, map_inv, FirstFusion.inclusion_t,
    show inclusion a = tableA from generatorA_eq_table,
    show inclusion b = tableB from generatorB_eq_table]
  decide +kernel

private theorem transport_inverter (r s α : MulAut Carrier)
    (h : r (s b) = (s b)⁻¹) :
    (α * r * α⁻¹) ((α * s) b) = ((α * s) b)⁻¹ := by
  change α (r (α.symm (α (s b)))) = (α (s b))⁻¹
  rw [α.symm_apply_apply, h, map_inv]

/-- Every involutory automorphism inverts an automorphic image of the same
literal cubic generator, including both inner classes and the outer class. -/
theorem exists_inverted_generator (r : MulAut Carrier) (hr : orderOf r = 2) :
    ∃ α : MulAut Carrier, r (α b) = (α b)⁻¹ := by
  classical
  by_cases hi : ∃ x : Carrier, r = MulAut.conj x
  · rcases InnerInvolutionCores.inner_involution_representatives r hr hi with
      ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact ⟨MulAut.conj g * MulAut.conj firstConjugator,
        transport_inverter (MulAut.conj a) (MulAut.conj firstConjugator)
          (MulAut.conj g) first_inverts⟩
    · exact ⟨MulAut.conj g * MulAut.conj secondConjugator,
        transport_inverter (MulAut.conj FirstFusion.t) (MulAut.conj secondConjugator)
          (MulAut.conj g) second_inverts⟩
  · let x := extensionEquivAut.symm r
    have hx : orderOf x = 2 :=
      (orderOf_injective extensionEquivAut.symm.toMonoidHom
        extensionEquivAut.symm.injective r).trans hr
    have ho : x ∉ intoExtension.range := by
      rintro ⟨y, hy⟩
      apply hi
      refine ⟨y, ?_⟩
      have he := congrArg extensionEquivAut hy
      simpa only [extensionEquivAut_intoExtension, x,
        MulEquiv.apply_symm_apply] using he.symm
    obtain ⟨g, hg⟩ := isConj_iff.mp
      (OuterInvolutionFusion.extension_outer_involution_fusion x hx ho)
    have he := congrArg extensionEquivAut hg
    have he' : extensionEquivAut g * involutionAut * (extensionEquivAut g)⁻¹ = r := by
      simpa only [map_mul, map_inv, extensionEquivAut_involution, x,
        MulEquiv.apply_symm_apply] using he
    rw [← he']
    exact ⟨extensionEquivAut g * 1,
      transport_inverter involutionAut 1 (extensionEquivAut g) involutionAut_b⟩

end Representation.JankoTwo.SmallBinaryDegrees.InvertingCubic
