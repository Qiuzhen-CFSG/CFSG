module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.RootGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Root-plane geometry in the original Chapter 12 linear branch

The whole-residual linear comparison identifies the two original cores as the
planes in one copy of UT₃(F). Their normalizers and centralizers are computed
in the original ambient group. The second theorem applies this geometry to the
actual involution centralizer: only containment of its two-core in S remains
as a premise for the three-way core alternative.

This includes field four and both amalgam orientations. It does not establish
ambient recognition or GlobalExit. Full-normalizer realization, centralizer
control, weak closure in T, and completion recognition remain with this task.
Source: Aschbacher–Smith 5.3.5–7, printed pp.660–661, applied in Chapter12 on
p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
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

/-- The original Chapter12 cores generate S, intersect in Z(S), and each has
its full ambient normalizer and centralizer determined. -/
theorem rankOne_global_linear_root_geometry :
    m = n ∧ Global.sourceS L H = L.pCoreIn 2 ⊔ (residual H).pCoreIn 2 ∧
    (center (Global.sourceS L H)).map (Global.sourceS L H).subtype =
      L.pCoreIn 2 ⊓ (residual H).pCoreIn 2 ∧
    normalizer (L.pCoreIn 2 : Set G) = normalizer (L : Set G) ∧
    normalizer ((residual H).pCoreIn 2 : Set G) = normalizer (residual H : Set G) ∧
    centralizer (L.pCoreIn 2 : Set G) = L.pCoreIn 2 ∧
    centralizer ((residual H).pCoreIn 2 : Set G) = (residual H).pCoreIn 2 ∧
    centralizer (Global.sourceS L H : Set G) =
      (center (Global.sourceS L H)).map (Global.sourceS L H).subtype := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hN := d.linear_root_normalizers hi hH hp F hm hF he hmax
  have hC := d.linear_root_centralizers hi hH hp F hm hF he hmax
  exact ⟨(d.linear_core_structure hi hH hp F hm hF he).1,
    d.linear_sourceS_eq_sup_cores hi hH hp F hm hF he hmax,
    (d.linear_involution_geometry hi hH hp F hm hF he hmax).1,hN.1,hN.2.1,hC.1,hC.2,
    d.linear_sourceS_centralizer hi hH hp F hm hF he hmax⟩

/-- The marked matrix geometry supplies the core alternative for the actual
Chapter12 centralizer, conditional on its source containment O₂(C_G(z)) ≤ S. -/
theorem rankOne_global_linear_centralizer_core_alternative
    (z : G) (hz : orderOf z = 2)
    (hzS : z ∈ (center (Global.sourceS L H)).map (Global.sourceS L H).subtype)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ Global.sourceS L H) :
    (center (Global.sourceS L H)).map (Global.sourceS L H).subtype =
      ((omega₁ (center ((centralizer ({z} : Set G)).pCoreIn 2)) (p := 2)).map
        (center ((centralizer ({z} : Set G)).pCoreIn 2)).subtype).map
          ((centralizer ({z} : Set G)).pCoreIn 2).subtype ∨
    (centralizer ({z} : Set G)).pCoreIn 2 = L.pCoreIn 2 ∨
    (centralizer ({z} : Set G)).pCoreIn 2 = (residual H).pCoreIn 2 :=
  d.linear_centralizer_core_alternative (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax z hz hzS hzT hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
