module
public import CFSG.Quasithin.Chapter10.SourceA5OffenderFixedGeometry
public import Theory.GroupTheory.ConjugatePairCommutation

/-!
# Commutation of the original small-corank conjugates

Universal placement and centralization of the conjugate moved factor imply
commutation of the full module with every small-corank conjugate. The original
pair decomposition supplies the two factors; four literal conjugators recover
centralization of both. Conjugates already in M have corank zero, so the same
chosen bound applies throughout the argument.

The independent numerical centralization and rank-kernel placement results
supply the sole universal factor input. No active-factor choice or equality
between the different factor centralizers is assumed.

Source: Aschbacher--Smith, quasithin 10.2.12, printed pp.754–755.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Universal moved-factor placement and centralization imply commutation of
every small-corank full-module conjugate. The conjugation assembly uses no
active-factor choice and no equality of the two module centralizers. -/
theorem source_a5_small_conjugates_commute_of_moved_factor
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (k : ℕ)
    (hfactor : ∀ g : G, g ∉ D.maximalLocal →
      subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
        (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k →
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤ D.maximalLocal ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
        centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (g : G)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k) :
    ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  by_cases hg : g ∈ D.maximalLocal
  · have he : D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hg)
    rw [he]
    have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal
    let := D.fullModule_elementary hu
    exact commutator_eq_bot_iff_le_centralizer.mpr D.fullModule.le_centralizer
  · have htM : t ∈ D.maximalLocal := le_normalizer_componentOrbit L T ht
    exact conjugate_commutator_eq_bot_of_pair_factor D.maximalLocal D.fullModule
      ⁅D.fullModule,L⁆ t htM (D.maximalLocal_normalizes_fullModule htM)
      (source_nonnormal_fullModule_eq_moved_pair D hn ht hcross)
      (fun X => subgroupCorank X (X ⊓ D.maximalLocal) ≤ k)
      (fun X hXM => by simp [inf_eq_left.mpr hXM,subgroupCorank])
      hfactor g hg hsmall

end CFSG.Quasithin.Chapter10
