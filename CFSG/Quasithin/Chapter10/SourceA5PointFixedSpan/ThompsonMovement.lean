module
public import CFSG.Quasithin.Chapter10.SourceA5PointFixedSpan
public import CFSG.Quasithin.Chapter10.SourceA5PointThompsonMovement

/-!
# Fixed-span discharge in the Thompson movement consumer

The chosen irreducible A5 marking supplies the literal fixed-span premise
in the original point-component Thompson argument. Equality of the point
and ambient Thompson groups remains the independent local Sylow input.
Source: Aschbacher–Smith10.2.9, printed p.751.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The original fixed-span premise is discharged in the actual constrained
Thompson movement theorem, using the chosen irreducible module. -/
theorem source_a5_point_thompson_not_centralizes_of_irreducible
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (I : Subgroup G) (hLI : L ≤ I)
    (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))
    (hJP : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      elementaryAbelianMaxJ (T : Subgroup G))
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    ¬ elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ≤
      centralizer (conjugateSpanBy
        (⁅D.fullModule,L⁆ ⊓ centralizer
          ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I : Set G) := by
  exact source_a5_point_thompson_not_centralizes D hn ht hcross I hLI hout hCW hs hJP
    (source_a5_point_component_fixed_span_contains D e hi hn hvL hv0 I hLI) hr
end CFSG.Quasithin.Chapter10
