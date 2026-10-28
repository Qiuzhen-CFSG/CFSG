module
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.Transport
public import CFSG.Quasithin.Chapter10.SourceA5PointFixedSpan.ThompsonMovement
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion

/-!
# Point-centralizer consumers of the fixed-vector orbit geometry

An M-conjugate of Baum(T) fixing a locally saturated point supplies both
its full Sylow subgroup and the original Thompson equality. These facts
remove the promotion and Thompson premises in the literal constrained
component argument. The separate natural and deleted representation
proofs construct the orbit representatives.

Source: Aschbacher–Smith10.2.9, printed pp.750–751.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- Point stabilization is the exact premise required for the fixed span;
this form also applies to points fixed by the whole component orbit. -/
theorem source_a5_point_component_fixed_span_of_stabilizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {v : G}
    (hPL : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G))
    (I : Subgroup G) (hLI : L ≤ I) :
    ⁅D.fullModule,L⁆ ≤ conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
      (((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) I := by
  have hs := source_a5_moved_fixed_span D e hi _
    (inf_le_left.trans (le_normalizer_componentOrbit L T)) hPL
    (T.isPGroup'.to_le inf_le_left)
  calc
    ⁅D.fullModule,L⁆ = conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer
        (((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G)) L := hs.symm
    _ ≤ _ := conjugateSpanBy_mono le_rfl hLI

/-- Source row geometry supplies the exact Sylow and Thompson premises in
the literal constrained point-component movement argument. -/
theorem source_a5_point_thompson_movement_of_source_orbits
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ D.fullModule) (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (h1021 : normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G)))
    (hbranch : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) ∨
      ∃ m ∈ D.maximalLocal,
        (baumann (T : Subgroup G)).map (MulAut.conj m).toMonoidHom ≤ centralizer ({v} : Set G))
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    ¬ elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ≤
      centralizer (conjugateSpanBy
        (⁅D.fullModule,L⁆ ⊓ centralizer
          ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I : Set G) := by
  obtain ⟨hSyl,hJ⟩ := source_point_sylow_and_thompson_of_source_alternatives D h1021 hv hs hbranch
  exact source_a5_point_thompson_not_centralizes_of_irreducible D e hi hn ht hvL hv0
    hcross I hLI hout hCW (hSyl.restrict le_sup_right (sup_le hIX inf_le_right)) hJ hr

/-- Source row geometry supplies the exact Sylow and Thompson premises in
the literal constrained point-component movement argument. -/
theorem source_a5_point_thompson_movement_of_stabilizes_and_source_orbits
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ D.fullModule)
    (hPL : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (h1021 : normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G)))
    (hbranch : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) ∨
      ∃ m ∈ D.maximalLocal,
        (baumann (T : Subgroup G)).map (MulAut.conj m).toMonoidHom ≤ centralizer ({v} : Set G))
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    ¬ elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ≤
      centralizer (conjugateSpanBy
        (⁅D.fullModule,L⁆ ⊓ centralizer
          ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I : Set G) := by
  obtain ⟨hSyl,hJ⟩ := source_point_sylow_and_thompson_of_source_alternatives D h1021 hv hs hbranch
  exact source_a5_point_thompson_not_centralizes D hn ht hcross I hLI hout hCW
    (hSyl.restrict le_sup_right (sup_le hIX inf_le_right)) hJ
    (source_a5_point_component_fixed_span_of_stabilizes D e hi hPL I hLI) hr

/-- The original endpoint after the row-specific Baumann orbit geometry;
its Sylow-promotion premise is discharged. -/
theorem source_a5_moved_point_centralizers_of_source_orbits
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hNW : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hfixed : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∈ centralizer (localOrbit T L : Set G) → centralizer ({v} : Set G) ≤ D.maximalLocal)
    (h1021 : normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (horbits : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∉ centralizer (localOrbit T L : Set G) →
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) ∨
        ∃ m ∈ D.maximalLocal,
          (baumann (T : Subgroup G)).map (MulAut.conj m).toMonoidHom ≤
            centralizer ({v} : Set G))
    (hinspect : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∉ centralizer (localOrbit T L : Set G) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) → SourceA5PointComponentInspection D e t v) :
    ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal := by
  apply source_a5_moved_point_centralizers_of_inspection D e hn ht htn hsep hcross hNL hNW hfixed
    (fun v hv hvne hv0 hs => ?_) hinspect
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have htV : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
      (le_normalizer_componentOrbit L T ht))
  have hvV : v ∈ D.fullModule := htV ▸ map_mono hWV hv
  exact (source_point_sylow_and_thompson_of_source_alternatives D h1021 hvV hs
    (horbits v hv hvne hv0)).1

end CFSG.Quasithin.Chapter10
