module

public import Theory.Mathieu.M11.Properties.OuterRestriction.Finite
public import Theory.Mathieu.M11.Properties.InvolutionClasses
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.CyclicNormalOddQuotient

/-!
# The outer automorphism group of M11

Every abstract automorphism of the concrete Witt-design group is inner.
First conjugate its image of the standard involution back to that involution.
The remaining generator satisfies three short identities. The exhaustive
Schreier-coordinate calculation shows that its image is conjugate by an
element centralizing the first generator; generation then identifies the
automorphism. In particular the outer group satisfies the cyclic-normal,
odd-quotient restriction used in the quasithin classification.

Source: GLS3, Table 5.3a (Out(M11) = 1); Aschbacher–Smith, combined
1 March 2004 manuscript, printed pp.33 and 510.
-/

namespace Sporadic.Mathieu
open M11Outer

private theorem generatorB_fourth : m11GeneratorBInM11 ^ 4 = 1 := by
  apply Subtype.ext
  change m11GeneratorB ^ 4 = 1
  simpa only [m11GeneratorB_order] using pow_orderOf_eq_one m11GeneratorB

private theorem generatorAB_eleventh :
    (m11GeneratorAInM11 * m11GeneratorBInM11) ^ 11 = 1 := by
  apply Subtype.ext
  change (m11GeneratorA * m11GeneratorB) ^ 11 = 1
  simpa only [m11GeneratorAB_order] using
    pow_orderOf_eq_one (m11GeneratorA * m11GeneratorB)

set_option maxRecDepth 100000 in
private theorem generator_word :
    rigidityWord m11GeneratorAInM11 m11GeneratorBInM11 ^ 3 = 1 := by
  apply Subtype.ext
  change rigidityWord m11GeneratorA m11GeneratorB ^ 3 = 1
  decide +kernel

private theorem aut_eq_of_generator_images (a b : MulAut M11)
    (ha : a m11GeneratorAInM11 = b m11GeneratorAInM11)
    (hb : a m11GeneratorBInM11 = b m11GeneratorBInM11) : a = b := by
  have h := MonoidHom.eq_of_eqOn_dense m11_generators_closure_eq_top
    (f := a.toMonoidHom) (g := b.toMonoidHom) (by
      intro x hx
      rcases hx with rfl | hx
      · exact ha
      · have : x = m11GeneratorBInM11 := hx
        subst x
        exact hb)
  exact MulEquiv.toMonoidHom_injective h

private theorem aut_fix_involution_inner (a : MulAut M11)
    (ha : a m11GeneratorAInM11 = m11GeneratorAInM11) :
    a ∈ MulAut.innerSubgroup M11 := by
  have hy : a m11GeneratorBInM11 ^ 4 = 1 := by
    rw [← map_pow, generatorB_fourth, map_one]
  have hab : (m11GeneratorAInM11 * a m11GeneratorBInM11) ^ 11 = 1 := by
    rw [← ha, ← map_mul, ← map_pow, generatorAB_eleventh, map_one]
  have hw : rigidityWord m11GeneratorAInM11 (a m11GeneratorBInM11) ^ 3 = 1 := by
    have h := congrArg a generator_word
    simpa only [rigidityWord, map_pow, map_mul, map_inv, map_one, ha] using h
  obtain ⟨c, hc, hyc⟩ := image_rigidity _ hy hab hw
  refine ⟨c, aut_eq_of_generator_images _ _ ?_ ?_⟩
  · exact hc.trans ha.symm
  · exact hyc

/-- Every abstract automorphism of the concrete Witt-design group M11 is inner. -/
public theorem m11_automorphism_inner (a : MulAut M11) :
    a ∈ MulAut.innerSubgroup M11 := by
  have ha : orderOf (a m11GeneratorAInM11) = 2 := by
    rw [a.orderOf_eq, m11GeneratorAInM11_order]
  obtain ⟨g, hg⟩ := isConj_iff.mp (m11_involution_isConj_generatorA _ ha)
  have hn := aut_fix_involution_inner (MulAut.conj g * a) hg
  have hi : MulAut.conj g ∈ MulAut.innerSubgroup M11 := ⟨g, rfl⟩
  have h := (MulAut.innerSubgroup M11).mul_mem
    ((MulAut.innerSubgroup M11).inv_mem hi) hn
  simpa only [inv_mul_cancel_left] using h

/-- The actual quotient Aut(M11)/Inn(M11) is trivial. -/
public theorem m11_outer_subsingleton : Subsingleton (MulAut.Outer M11) := by
  have hone (x : MulAut.Outer M11) : x = 1 := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup M11) x
    exact (QuotientGroup.eq_one_iff a).mpr (m11_automorphism_inner a)
  exact ⟨fun x y => (hone x).trans (hone y).symm⟩

/-- The two-group outer restriction needed by the quasithin consumer. -/
public theorem m11_outer_isPGroup_two : IsPGroup 2 (MulAut.Outer M11) := by
  let := m11_outer_subsingleton
  intro a
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The cyclic normal odd-quotient restriction for the full outer group of M11. -/
public theorem m11_outer_hasCyclicNormalOddQuotient :
    Theory.GroupTheory.HasCyclicNormalOddQuotient (MulAut.Outer M11) :=
  Theory.GroupTheory.hasCyclicNormalOddQuotient_of_isPGroup_two m11_outer_isPGroup_two

end Sporadic.Mathieu
