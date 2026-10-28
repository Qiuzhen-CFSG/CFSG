module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.SylowIntersection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient.AmbientGeneration

/-!
# The three original Sylow-intersection cases

The prepared maximal linear row gives source F.4.48 in the original group:
disjoint Sylows have odd central-involution product; a root-plane intersection
is the span of their two central lines and gives product order two; otherwise
the intersection is a third central line and the product has order four.
Conjugate central lines in the Sylow lie in its two root planes, and a central
line determines the unique root plane through it in each original orbit.

These literal Chapter12 applications retain n>1, field four, both orientations,
and the full original Sylows. They supply the remaining intersection geometry
for Suzuki's Hall-normalizer count; that count and cube membership in the whole
overlap are still needed for ambient recognition and GlobalExit.
Source: Aschbacher–Smith F.4.48–49, pp.298–299, applied to 12.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (d : Global.Preparation T L H A B (residual H))
  (hp : Group.IsPerfect (residual H))
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (he : Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F).reverse))
  (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include D h hmany hn hpsl hH d hp hm hF he hmax

/-- All three F.4.48 alternatives hold for the unchanged chosen-module input. -/
theorem rankOne_global_linear_sylow_intersection_trichotomy
    (z : G) (hz : orderOf z=2) (hzZ : z ∈ centerIn (Global.sourceS L H))
    (g : G) (hg : g ∉ normalizer (T : Set G)) :
    (Disjoint (T : Subgroup G) ((T : Subgroup G).conjBy g) ∧
      Odd (orderOf (z*(g*z*g⁻¹)))) ∨
    (∃ i : Fin 2,
      (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g = (![L,residual H] i).pCoreIn 2 ∧
      centerIn (Global.sourceS L H) ⊔ (centerIn (Global.sourceS L H)).conjBy g =
        (![L,residual H] i).pCoreIn 2 ∧ orderOf (z*(g*z*g⁻¹))=2) ∨
    ((∃ a : G, (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g =
      (centerIn (Global.sourceS L H)).conjBy a) ∧
      (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g ≠ centerIn (Global.sourceS L H) ∧
      (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g ≠ (centerIn (Global.sourceS L H)).conjBy g ∧
      orderOf (z*(g*z*g⁻¹))=4) :=
  d.linear_sylow_intersection_trichotomy (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax z hz hzZ g hg

/-- The central-line intersections belong to the actual original root planes. -/
theorem rankOne_global_linear_central_line_in_sylow (g : G)
    (hg : (centerIn (Global.sourceS L H)).conjBy g ≤ (T : Subgroup G)) :
    ∃ i : Fin 2, (centerIn (Global.sourceS L H)).conjBy g ≤ (![L,residual H] i).pCoreIn 2 :=
  d.linear_central_line_in_sylow (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax g hg

/-- A conjugate central line determines its unique plane in each original orbit. -/
theorem rankOne_global_linear_root_plane_through_conjugate_center (i : Fin 2) (a b : G)
    (hab : (centerIn (Global.sourceS L H)).conjBy a ≤ ((![L,residual H] i).pCoreIn 2).conjBy b) :
    ((![L,residual H] i).pCoreIn 2).conjBy a = ((![L,residual H] i).pCoreIn 2).conjBy b :=
  d.linear_root_plane_through_conjugate_center (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax i a b hab

/-- The root-plane Sylow-intersection case lies in an original full factor
normalizer, as required for Suzuki's local coset calculation. -/
theorem rankOne_global_linear_commuting_sylow_intersection_local
    (z : G) (hz : orderOf z=2) (hzZ : z ∈ centerIn (Global.sourceS L H))
    (g : G) (hg : g ∉ normalizer (T : Set G))
    (hcomm : Commute z (g*z*g⁻¹)) :
    ∃ i : Fin 2, g ∈ normalizer (![L,residual H] i : Set G) ∧
      (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g = (![L,residual H] i).pCoreIn 2 ∧
      centerIn (Global.sourceS L H) ⊔ (centerIn (Global.sourceS L H)).conjBy g =
        (![L,residual H] i).pCoreIn 2 ∧ orderOf (z*(g*z*g⁻¹))=2 :=
  d.linear_commuting_sylow_intersection_local (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax z hz hzZ g hg hcomm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
