module

public import Theory.Mathieu.M24.Properties.OuterRestriction.Normalizer
public import Theory.Mathieu.M24.Properties.OuterRestriction.PointStabilizers
public import Theory.GroupTheory.CyclicNormalOddQuotient
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The outer automorphisms of the concrete M24

The concrete Witt-design group is self-normalizing in Sym(24). Every abstract
automorphism preserves its point-stabilizer class: the concrete M23 has a
fixed point in every action on 24 points. The transitive permutation action
therefore reconstructs each abstract automorphism as conjugation by a design
automorphism. Consequently Aut(M24)/Inn(M24) is trivial.

This proves Out(M24) = 1 in GLS3, Table 5.3e, and the M24 case of Aschbacher,
*Sporadic Groups*, Chapter 7, Exercise 5, printed p.107.
The cyclic normal odd-quotient corollary supplies the restriction used in
Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.510, for the M24
entry of Theorem C on printed p.33. All reconstruction premises are discharged
for the original Witt-design carrier; the conditional reductions remain available.
-/

namespace Sporadic.Mathieu.M24OuterRestriction

/-- Reconstruction from the actual point-stabilizer class makes every
abstract automorphism inner. The permutation normalizer is already computed. -/
public theorem conj_surjective_of_stabilizers
    (hstab : ∀ f : MulAut M24, ∃ x : Fin 24,
      (MulAction.stabilizer M24 (24 : Fin 24)).map f.toMonoidHom =
        MulAction.stabilizer M24 x) :
    Function.Surjective (MulAut.conj : M24 →* MulAut M24) :=
  Subgroup.conj_surjective_of_stabilizers_of_normalizer M24 (24 : Fin 24)
    hstab normalizer_eq

/-- The point-stabilizer reconstruction premise implies that the actual
outer automorphism quotient is a two-group. -/
public theorem outer_isPGroup_two_of_stabilizers
    (hstab : ∀ f : MulAut M24, ∃ x : Fin 24,
      (MulAction.stabilizer M24 (24 : Fin 24)).map f.toMonoidHom =
        MulAction.stabilizer M24 x) :
    IsPGroup 2 (MulAut.Outer M24) := by
  intro x
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup M24) x
  obtain ⟨g, rfl⟩ := conj_surjective_of_stabilizers hstab f
  refine ⟨0, ?_⟩
  simp only [pow_zero, pow_one]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩

/-- Conditional M24 outer-group restriction for the quasithin inspection.
The unconditional theorem below discharges the reconstruction premise. -/
public theorem cyclicNormalOddQuotient_of_stabilizers
    (hstab : ∀ f : MulAut M24, ∃ x : Fin 24,
      (MulAction.stabilizer M24 (24 : Fin 24)).map f.toMonoidHom =
        MulAction.stabilizer M24 x) :
    Theory.GroupTheory.HasCyclicNormalOddQuotient (MulAut.Outer M24) :=
  Theory.GroupTheory.hasCyclicNormalOddQuotient_of_isPGroup_two
    (outer_isPGroup_two_of_stabilizers hstab)

/-- Every abstract automorphism of the concrete M24 is inner. -/
public theorem conj_surjective :
    Function.Surjective (MulAut.conj : M24 →* MulAut M24) :=
  conj_surjective_of_stabilizers point_stabilizers_map

/-- The actual outer automorphism quotient of the Witt-design group is trivial. -/
public theorem outer_subsingleton : Subsingleton (MulAut.Outer M24) := by
  have hone (x : MulAut.Outer M24) : x = 1 := by
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup M24) x
    exact (QuotientGroup.eq_one_iff f).mpr (conj_surjective f)
  exact ⟨fun x y => (hone x).trans (hone y).symm⟩

/-- The outer group of the concrete M24 is a two-group. -/
public theorem outer_isPGroup_two : IsPGroup 2 (MulAut.Outer M24) :=
  outer_isPGroup_two_of_stabilizers point_stabilizers_map

/-- The M24 outer-group restriction for the quasithin inspection. -/
public theorem cyclicNormalOddQuotient :
    Theory.GroupTheory.HasCyclicNormalOddQuotient (MulAut.Outer M24) :=
  cyclicNormalOddQuotient_of_stabilizers point_stabilizers_map

end Sporadic.Mathieu.M24OuterRestriction
