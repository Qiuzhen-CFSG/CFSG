module

public import Theory.SpecificGroups.PSL3Three.RepresentativeBounds
public import Theory.SpecificGroups.PSL3Three.NodeExtensions

/-!
# Proper-subgroup cover for `SL₃(3)`

The checked fifty-one-node extension certificate enumerates every subgroup of the
finite matrix group up to conjugacy.  The representative bounds put every
proper node in one of the four concrete subgroups from `Subgroups`, while the
top node is excluded for a proper input.  Consequently every proper subgroup
is contained in a conjugate of one of the line, plane, monomial, or Singer
normalizer candidates.

No subgroup order or external classification is used here: completeness is
the kernel-checked `node_extensionClosed` certificate and the finite matrix
model supplies the `Finite SL` instance.

Source: GLS III, Theorem 6.5.3(a–c), with the proper-subgroup restriction.
-/

namespace Matrix.PSL3Three

open Theory.GroupTheory.SubgroupEnumeration
open CertifiedEnumeration

/-- Every proper subgroup of `SL₃(3)` lies in a conjugate of one of the four
concrete candidate subgroups. -/
public theorem proper_subgroup_le_conjugate (H : Subgroup SL) (hH : H ≠ ⊤) :
    ∃ j : Fin 4, ∃ g : SL,
      H ≤ (CertifiedEnumeration.candidate j).map (MulAut.conj g).toMonoidHom := by
  exact CertifiedEnumeration.proper_le_conjugate_of_extensionClosed
    CertifiedEnumeration.node_extensionClosed H hH

/-- The candidate index in `proper_subgroup_le_conjugate` can be expanded to
the four named subgroups defined in `Subgroups`. -/
public theorem proper_subgroup_le_named_conjugate (H : Subgroup SL) (hH : H ≠ ⊤) :
    (∃ g : SL, H ≤ lineStabilizerSL.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : SL, H ≤ planeStabilizerSL.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : SL, H ≤ monomialSL.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g : SL, H ≤ singerNormalizerSL.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨j, g, hg⟩ := proper_subgroup_le_conjugate H hH
  fin_cases j
  · exact Or.inl ⟨g, hg⟩
  · exact Or.inr (Or.inl ⟨g, hg⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨g, hg⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨g, hg⟩))

end Matrix.PSL3Three
