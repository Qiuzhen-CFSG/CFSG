module
public import CFSG.Quasithin.Chapter10.SourceA5PointFixedKernel.Completion
public import CFSG.Quasithin.Chapter10.SourceA5ConjugateIntersection

/-!
# The all-point centralizer endpoint in the original intersection argument

The fixed-kernel completion supplies point-centralizer control for the
literal moved factor. Original 10.2.10(1) then gives its trivial intersection
with every conjugate outside M. The independent all-point Sylow and
inspection inputs remain with their source producers.
Source: Aschbacher–Smith 10.2.9–10, printed pp.750–753.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual 10.2.10 consumer no longer needs a separate fixed-kernel
centralizer hypothesis. -/
theorem source_a5_moved_inf_conjugate_eq_bot_of_all_point_inspection
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hpromote : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (D.maximalLocal ⊓ centralizer ({v} : Set G)) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)))
    (hinspect : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) → SourceA5PointComponentInspection D e t v)
    {g : G} (hg : g ∉ D.maximalLocal) :
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hcent := source_a5_moved_point_centralizers_of_all_point_inspection
    D e ht htn hcross hpromote hinspect
  exact source_a5_moved_inf_conjugate_eq_bot D e hn t ht hcross hcent
    (source_a5_component_normalizer_le D e hn) hg

end CFSG.Quasithin.Chapter10
