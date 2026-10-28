module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionTypesAssembly
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionDisjoint

/-!
# An additional irreducible copy outside the chosen Sylow orbit

The original seed is irreducible when its L-fixed subgroup is trivial.
Every normalizer conjugate has the same invariant-subgroup minimality.
Intersecting an escaping conjugate with the literal Sylow orbit therefore
gives zero. Combined with the proved normalizer two-type reduction, every
strict enlargement supplies a same-type constituent disjoint from the
whole Sylow pair, with the original L-action unchanged.

This strengthens the repeated-copy boundary used by the source325 assembly.
The cubic exclusion of this additional copy remains with qt-baumann-fsu;
no homogeneity in the full normalizer orbit is assumed here.
Source: Aschbacher--Smith D.3.10, paragraph following D.3.11, printed p.201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- The literal fixed-free chosen seed has no proper nonzero L-invariant subgroup. -/
theorem seed_invariant_subgroup_eq (D : ChosenModule T L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (J : Subgroup G) (hJV : J ≤ V) (hLJ : L ≤ normalizer (J : Set G)) :
    J = ⊥ ∨ J = V := by
  let τ := D.seedRepresentation.comp D.componentImage.subtype
  let e : ActionEquiv τ τ := {
    groupEquiv := MulEquiv.refl _
    linearEquiv := LinearEquiv.refl _ _
    intertwines := fun _ _ => rfl }
  let c := D.seedConjugationCoordinates τ e
  have hi : IsIrreducible (τ.comp (e.groupEquiv.toMonoidHom.comp D.componentHom)) :=
    (irreducible_comp_surjective_iff _
      (e.groupEquiv.surjective.comp D.componentHom_surjective) τ).mpr (D.seed_irreducible hc)
  exact c.invariant_subgroup_eq hi J hJV hLJ

omit [Finite G] in
/-- A conjugate escaping the Sylow orbit is disjoint from that entire orbit. -/
theorem normalizer_conjugate_inf_sylowOrbit_eq_bot
    (D : ChosenModule T L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (g : normalizer (L : Set G))
    (hout : ¬ V.map (MulAut.conj g.val).toMonoidHom ≤ componentOrbit V (T : Subgroup G)) :
    V.map (MulAut.conj g.val).toMonoidHom ⊓ componentOrbit V (T : Subgroup G) = ⊥ := by
  let B := componentOrbit V (T : Subgroup G)
  let I := V.map (MulAut.conj g.val).toMonoidHom
  have hLB : L ≤ normalizer (B : Set G) := by
    change L ≤ normalizer (componentOrbit V (T : Subgroup G) : Set G)
    rw [←D.orbitSpace_image]
    exact (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left).trans
      (ReducedNormal.subspaceImage_normalized _ _
        (Homogeneous.orbitSpan_invariant _ ⊤ D.space))
  have hLI : L ≤ normalizer (I : Set G) := by
    rw [← map_equiv_normalizer_eq V (MulAut.conj g.val)]
    exact (mem_normalizer_iff_map_conj_eq.mp g.property).ge.trans (map_mono D.normalizes)
  apply (invariant_conjugate_subgroup_eq (D.seed_invariant_subgroup_eq hc) g
    (I ⊓ B) inf_le_left ((le_inf hLI hLB).trans inf_normalizer_le_normalizer_inf)).resolve_right
  intro he
  exact hout (he.symm.le.trans inf_le_right)

/-- A strict enlargement produces a whole additional irreducible copy, disjoint
from the entire Sylow orbit, with the original component action unchanged. -/
theorem exists_repeated_disjoint_conjugate_of_normalizerOrbit_ne
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠
      componentOrbit V (T : Subgroup G)) :
    ∃ g ∈ normalizer (L : Set G),
      SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) ∧
      V.map (MulAut.conj g).toMonoidHom ⊓ componentOrbit V (T : Subgroup G) = ⊥ ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ componentOrbit V (T : Subgroup G) := by
  obtain ⟨g,hg,he,_,hout⟩ := D.exists_repeated_conjugate_of_normalizerOrbit_ne h hmany hc hm hne
  exact ⟨g,hg,he,D.normalizer_conjugate_inf_sylowOrbit_eq_bot hc ⟨g,hg⟩ hout,hout⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
