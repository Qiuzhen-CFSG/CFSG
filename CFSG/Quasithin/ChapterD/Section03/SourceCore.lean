module

public import CFSG.Quasithin.ChapterD.Section03.SourceSetup
public import Theory.Representation.BinaryOffender.Homogeneous.Core

/-!
# Triviality of the two-core in the D.3 module setup

In either structural case the two-core centralizes the normal actor:
ordinary components centralize solvable normal subgroups, while distinct
normal prime-groups commute. The source core-invariance puts the two-core
in the seed stabilizer. A.1.41 kills its action there, and normality and
faithful orbit generation kill the entire two-core.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma D.3.4(1), first assertion, printed pp.193–194.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}
  {T : Sylow 2 G} {X : Subgroup G} {I : Submodule (ZMod 2) V}

/-- Both original actor alternatives centralize the two-core. -/
theorem ActorCases.twoCore_centralizes [X.Normal]
    {hn : (T : Subgroup G) ≤ normalizer (X : Set G)} (h : ActorCases T X hn) :
    pCore 2 G ≤ centralizer (X : Set G) := by
  rcases h with ⟨L, hL, rfl⟩ | ⟨p, hp, ho, hX, _⟩
  · have hLC : L ≤ centralizer (pCore 2 G : Set G) := by
      rcases hL.normal_dichotomy (pCore 2 G) with hl | hc
      · let := hL.2
        let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
        let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
        let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
        let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
          (inclusion_injective hl)
        exact (Group.IsPerfect.not_isSolvable L inferInstance).elim
      · exact commutator_eq_bot_iff_le_centralizer.mp hc
    apply le_centralizer_iff.mpr
    exact iSup_conjugates_le_of_le_normalizer _ _ _ hLC (by
      rw [normalizer_eq_top]
      exact le_top)
  · have hd : Disjoint (pCore 2 G) X :=
      IsPGroup.disjoint_of_coprime pCore_isPGroup hX ho.coprime_two_left
    exact commutator_eq_bot_iff_le_centralizer.mp
      (le_bot_iff.mp ((commutator_le_inf (pCore 2 G) X).trans_eq hd.eq_bot))

/-- D.3.4(1): the original faithful action has trivial two-core. -/
theorem SourceHypotheses.twoCore_eq_bot (h : SourceHypotheses K ρ T X I) :
    pCore 2 G = ⊥ := by
  let := h.finiteModule
  let := h.normal
  have hstab : pCore 2 G ≤ subspaceStabilizer ρ I :=
    (pCore_le_map_of_sylow_le T (X ⊔ (T : Subgroup G)) le_sup_right).trans
      h.coreInvariant
  have hfix := IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes ρ h.seed
    pCore_isPGroup h.cases.twoCore_centralizes hstab
  exact eq_bot_of_faithful_orbitSpan ρ h.faithful hfix h.generated

end CFSG.Quasithin.ChapterD.Section03
