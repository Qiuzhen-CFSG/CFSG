module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.Basic
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.Conjugacy.Geometry
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Component conjugacy from placement in the concrete pair normalizer

Once a conjugate of the maximal subgroup lies in the proper normalizer of
the canonical Suzuki pair, maximality makes these subgroups equal. Transport
the supplied C-component through that equality. The component calculation
in the concrete normalizer places it on one of the two full-parameter Levis;
the fixed Weyl word interchanging those Levis gives the required conjugator.

This is a conditional assembly. The global placement and concrete normalizer
calculations are not proved here, so `ComponentLeviConjugacy` remains open.
In particular, the calculation does not promote relative subnormality to
ambient subnormality or presume that the originally supplied components are
isomorphic or exhaust the components of the maximal subgroup.

Source: Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E, §2.2 and Proposition 2.3.
-/

public section

namespace ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification

open Subgroup

private theorem component_conjugacy_of_maximal_placement
    {G : Type*} [Group G] {M N A : Subgroup G}
    (hM : IsCoatom M) (hN : N ≠ ⊤)
    (hcomponents : ∀ S : Subgroup N, S.IsCComponent →
      ∃ n : G, (S.map N.subtype).map (MulAut.conj n).toMonoidHom = A)
    {L : Subgroup M} (hL : L.IsCComponent) (g : G)
    (hg : M.map (MulAut.conj g).toMonoidHom ≤ N) :
    ∃ k : G, (L.map M.subtype).map (MulAut.conj k).toMonoidHom = A := by
  have hmax : IsCoatom (M.map (MulAut.conj g).toMonoidHom) :=
    ((MulAut.conj g).mapSubgroup.isCoatom_iff M).mpr hM
  have heq : M.map (MulAut.conj g).toMonoidHom = N :=
    ((hmax.le_iff_eq hN).mp hg).symm
  let e : M ≃* N :=
    ((MulAut.conj g).subgroupMap M).trans (MulEquiv.subgroupCongr heq)
  obtain ⟨n, hn⟩ := hcomponents (L.map e.toMonoidHom) (hL.map_equiv e)
  refine ⟨n * g, ?_⟩
  have hmaps : (L.map e.toMonoidHom).map N.subtype =
      (L.map M.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [map_map, map_map]
    rfl
  rw [hmaps, map_map] at hn
  have hconj : (MulAut.conj n).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (n * g)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hconj] at hn
  exact hn

/-- Maximality and the actual interchange discharge the conjugacy conclusion
once the two separate geometric obligations have been established. -/
theorem componentLeviConjugacy_of_pairPlacement_of_normalizerGeometry
    (hplacement : SuzukiPairPlacement) (hgeometry : SuzukiPairNormalizerGeometry) :
    ComponentLeviConjugacy := by
  intro m hm M hM hsolv hR L K hL hK hne hc
  obtain ⟨g, hg⟩ := hplacement m hm M hM hsolv hR L K hL hK hne hc
  obtain ⟨hN, hcomponents⟩ := hgeometry m hm
  apply component_conjugacy_of_maximal_placement hM hN _ hL g hg
  intro S hS
  rcases hcomponents S hS with hA | hB
  · refine ⟨1, ?_⟩
    have hconjOne : (MulAut.conj (1 : Model m)).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      simp
    rw [hconjOne, map_id]
    exact hA
  · refine ⟨suzukiFactorSwap m, ?_⟩
    rw [hB]
    exact companionSuzukiLevi_map_swap m

end ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification
