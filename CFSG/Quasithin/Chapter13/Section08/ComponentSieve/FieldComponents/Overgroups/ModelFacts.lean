module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SourceList
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.RankReduction
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder

/-!
# Outer automorphisms of the remaining component models

Every carrier in the exact 13.8.21 list is centerless and has a two-group
of outer automorphisms. The binary linear cases use the checked inner/graph
coverage, A₆ has outer order four, and the full octonion group covers the
automorphisms of G₂(2)′ with quotient of order two. Transport uses actual
model equivalences, including the binary field normalization.

These facts supply the Sylow supplement in the unrestricted-overgroup
assembly; they do not assert the component classification itself.
Source: Aschbacher–Smith, 13.8.21(3), printed p.957.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups
open LinearThree.Geometry.ExternalComponentAction
open Atlas.G2.LieAutomorphismExtensions

private theorem center_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : center B = ⊥) : center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have he := (centerCongr e ⟨x,hx⟩).property
  change e x ∈ center B at he
  rw [h, mem_bot] at he
  exact e.map_eq_one_iff.mp he

private theorem binary_outer_two (n : ℕ) (hn : n = 4 ∨ n = 5) :
    IsPGroup 2 (MulAut.Outer PSL(n, ZMod 2)) := by
  have h : IsPGroup 2 (MulAut.Outer (BinaryLinear.OuterCyclic.LinearGroup n)) := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective _ x
    let q := QuotientGroup.mk' (MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup n))
    obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.inner_graph hn a
    have hi : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    refine ⟨1, ?_⟩
    change q a ^ 2 = 1
    rcases hg with rfl | rfl
    · rw [hi, one_pow]
    · rw [map_mul, hi, mul_one, ← map_pow, BinaryLinear.OuterCyclic.graphLinear_sq, map_one]
  exact h.of_equiv (MulAut.outerCongr
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < n))).symm

private theorem g2_outer_two : IsPGroup 2
    (MulAut.Outer (commutator (Atlas.G2.Model (ZMod 2)))) := by
  have hc : Nat.card (Atlas.G2.Model (ZMod 2) ⧸ BinaryDerived) = 2 ^ 1 := by
    rw [← index_eq_card, binaryDerived_eq]
    exact Atlas.G2.BinaryException.index_H
  have h : IsPGroup 2 (MulAut.Outer BinaryDerived) := by
    apply (IsPGroup.of_card hc).of_surjective (MulAut.outerAction BinaryDerived)
    intro q
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨g,rfl⟩ := binaryConjugation_surjective a
    exact ⟨QuotientGroup.mk g, rfl⟩
  exact h

/-- Every remaining source model is centerless and has a two-group of outer automorphisms. -/
theorem remaining_model_facts {A : Type*} [Group A] [Finite A]
    (h : RemainingQuotient A) : center A = ⊥ ∧ IsPGroup 2 (MulAut.Outer A) := by
  have hs := RankReduction.smallQuotient_of_source_list h
  have hz : center A = ⊥ := by
    rcases RankReduction.small_quotient_alternative
      Atlas.G2.LieAutomorphismExtensions.binaryConjugation_surjective hs with he | h
    · obtain ⟨e⟩ := he
      exact center_transport e Matrix.PSL3Two.Automorphisms.center_psl_eq_bot
    · exact h.1
  refine ⟨hz, ?_⟩
  unfold RankReduction.SmallQuotient at hs
  rcases hs with ⟨n,hn,hn',⟨e⟩⟩ | he | he | he
  · apply IsPGroup.of_equiv (ϕ := (MulAut.outerCongr e).symm)
    by_cases h3 : n = 3
    · subst n
      exact Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv
        (MulAut.outerCongr Matrix.PSL3Two.equiv)
    · exact binary_outer_two n (by omega)
  · obtain ⟨e⟩ := he
    exact (IsPGroup.of_card (p := 2) (n := 2) AlternatingSix.ShadowLocal.outer_card).of_equiv
      (MulAut.outerCongr e).symm
  · obtain ⟨e⟩ := he
    exact alternatingGroup.SevenComponent.outer_two.of_equiv (MulAut.outerCongr e).symm
  · obtain ⟨e⟩ := he
    exact g2_outer_two.of_equiv (MulAut.outerCongr e).symm

/-- Transport the remaining-model facts to a literal component image or a
relative intrinsic quotient through its proved group equivalence. -/
theorem remaining_model_facts_of_equiv {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (e : A ≃* B) (h : RemainingQuotient B) :
    center A = ⊥ ∧ IsPGroup 2 (MulAut.Outer A) :=
  ⟨center_transport e (remaining_model_facts h).1,
    (remaining_model_facts h).2.of_equiv (MulAut.outerCongr e).symm⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups
