module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.Orbits
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.Normalizer
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.Transport

/-!
# The rank-one point-Sylow normalizer, including fixed vectors

The literal rank-one natural cover provides a Baumann conjugate fixing every
opposite vector. Local Sylow saturation and Baumann weak closure move this
conjugate into the original point Sylow. Its normalizer therefore lies in M,
and that Sylow is also Sylow in the full point centralizer. This step does
not require fixation of the full component-fixed layer by the half-Sylow.
Source: Aschbacher--Smith, 10.2.9, printed p.750.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original Baumann subgroup fixes each locally saturated opposite point. -/
theorem baumann_fixes_saturated_point
    (hmodel : RankOneNatural D)
    {t : G} (ht : t ∈ (T : Subgroup G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    ChapterB.baumann (T : Subgroup G) ≤ centralizer ({v} : Set G) :=
  source_point_baumann_fixed_of_conjugate_fixed D hs
    (partner_baumann_conjugate_fixed_of_rankOneNatural D hmodel ht hv)

/-- Both Sylow conclusions used before enlarging the original component hold
for every saturated point, including points fixed by L₀. -/
theorem point_sylow_normalizer_and_sylow
    (hnotA5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : RankOneNatural D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    normalizer (((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G) ≤
      D.maximalLocal ∧
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)) := by
  have hB := baumann_fixes_saturated_point D hmodel ht hv hs
  have hN := baumann_normalizer_le D hnotA5 hmodel (fun hn => htn (hn ht))
  exact ⟨source_element_sylow_normalizer_of_baumann_centralizes D hN hB,
    source_element_sylow_of_baumann_centralizes D hN hB hs⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
