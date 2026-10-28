module

public import Theory.GroupTheory.PGroup.C4SquareCubicExtension
public import Theory.GroupTheory.ElementaryEightIndexTwoGeometry

/-!
# Assembly of the abelian-critical-sixteen local geometry

The algebraic reduction and the elementary-eight normalizer calculation are
separate mathematical steps. The reduction produces an index-four cubic core
and its inverting overgroup whenever an involution is not central. The local
calculation converts this algebraic extension into the geometry used by fusion
and transfer. This module owns their assembly.

The theorem below makes these two remaining steps explicit. Initial action
reductions and the outside elementary-eight centralizer are proved in the
imported lower modules; no extension classification is assumed there.

Source: MacWilliams, Trans. AMS 150 (1970), Case 1.2, Lemma 3 and
(xxi)–(xxiv), printed pp.380–384, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace IsCriticalPSubgroup

/-- Assemble local geometry from the algebraic extension reduction and the
normalizer calculation. The two premises are isolated for independent proofs. -/
public theorem centrality_or_geometry_of_cubic_extension_reduction
    {P : Type*} [Group P] (C : Subgroup P) (a : MulAut P)
    (hext : (¬ ∀ x : P, orderOf x = 2 → x ∈ Subgroup.center P) →
      ∃ (R : Subgroup P) (t : P), C4SquareCubicInvertingExtension C R a t)
    (hgeom : ∀ (R : Subgroup P) (t : P),
      C4SquareCubicInvertingExtension C R a t → ElementaryEightIndexTwoGeometry R t) :
    (∀ x : P, orderOf x = 2 → x ∈ Subgroup.center P) ∨
      ∃ (R : Subgroup P) (t : P), ElementaryEightIndexTwoGeometry R t := by
  by_cases hc : ∀ x : P, orderOf x = 2 → x ∈ Subgroup.center P
  · exact Or.inl hc
  · obtain ⟨R, t, h⟩ := hext hc
    exact Or.inr ⟨R, t, hgeom R t h⟩

end IsCriticalPSubgroup
