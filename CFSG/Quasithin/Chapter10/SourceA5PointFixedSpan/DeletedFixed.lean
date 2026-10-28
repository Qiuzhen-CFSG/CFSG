module
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.Alternatives

/-!
# Zero-kernel fixed-vector discharge

A vector on the conjugate moved factor fixed by the full component orbit
pulls back into the original fixed kernel. If that kernel is trivial, the
vector is trivial. This removes the fixed-vector-control premise from the
literal point-centralizer endpoint, covering the deleted-module row.
Source: Aschbacher–Smith10.2.9, printed pp.750–751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A fixed vector on the partner factor vanishes when the original fixed kernel does. -/
theorem source_a5_partner_fixed_eq_one_of_moved_fixed_eq_bot
    (hz : sourceMovedFixed D = ⊥)
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hfix : v ∈ centralizer (localOrbit T L : Set G)) : v = 1 := by
  obtain ⟨w,hw,rfl⟩ := hv
  have hwZ : w ∈ sourceMovedFixed D := by
    refine ⟨hw,?_⟩
    intro l hl
    apply (MulAut.conj t).injective
    simp only [map_mul]
    exact hfix _ ((mem_normalizer_iff.mp (le_normalizer_componentOrbit L T ht) l).mp
      (le_componentOrbit L T hl))
  have hw1 : w = 1 := mem_bot.mp (hz ▸ hwZ)
  rw [hw1,map_one]

/-- The source point-centralizer endpoint with its fixed-vector premise discharged
for the zero-kernel row. Sylow promotion and inspection remain separate inputs. -/
theorem source_a5_moved_point_centralizers_of_inspection_of_moved_fixed_eq_bot
    (hz : sourceMovedFixed D = ⊥)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hNW : normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hpromote : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∉ centralizer (localOrbit T L : Set G) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (D.maximalLocal ⊓ centralizer ({v} : Set G)) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)))
    (hinspect : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∉ centralizer (localOrbit T L : Set G) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) → SourceA5PointComponentInspection D e t v) :
    ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal := by
  apply source_a5_moved_point_centralizers_of_inspection D e hn ht htn hsep hcross hNL hNW
    (fun v hv hvne hfix => (hvne (source_a5_partner_fixed_eq_one_of_moved_fixed_eq_bot D hz ht hv hfix)).elim)
    hpromote hinspect
end CFSG.Quasithin.Chapter10
