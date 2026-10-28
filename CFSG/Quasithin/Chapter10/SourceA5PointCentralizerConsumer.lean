module
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion
public import CFSG.Quasithin.Chapter10.SourceA5ConjugateIntersection
/-!
# Consumer of the original A5 point-centralizer endpoint

The completed point-centralizer inspection supplies the element-centralizer
hypothesis required by the 10.2.10 conjugate-intersection theorem. This thin
adapter keeps the earlier normalizer and source-inspection premises literal,
then transports the result to the original moved factor.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The point-centralizer endpoint feeds the original 10.2.10(1) intersection
bound without changing the literal quotient, actor, or conjugation map. -/
theorem source_a5_moved_inf_conjugate_eq_bot_of_inspection
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
      centralizer (L : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hNW : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hfixed : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∈ centralizer (localOrbit T L : Set G) → centralizer ({v} : Set G) ≤ D.maximalLocal)
    (hpromote : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∉ centralizer (localOrbit T L : Set G) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (D.maximalLocal ⊓ centralizer ({v} : Set G)) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)))
    (hinspect : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∉ centralizer (localOrbit T L : Set G) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) → SourceA5PointComponentInspection D e t v)
    {g : G} (hg : g ∉ D.maximalLocal) :
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ := by
  have hcent := source_a5_moved_point_centralizers_of_inspection D e hn ht htn
    hsep hcross hNL hNW hfixed hpromote hinspect
  exact source_a5_moved_inf_conjugate_eq_bot D e hn t ht hcross hcent hNL hg

end CFSG.Quasithin.Chapter10
