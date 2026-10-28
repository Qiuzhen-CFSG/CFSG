module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CentralFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Original chosen-module applications of linear centralizer geometry

The original Hypothesis1221 and chosen module produce the same rank-one
Input. The affine calculation then gives both full-normalizer intersection
bounds, transitivity on the original central line, and a Sylow-central
involution. The conditional centralizer theorem retains exactly the
individual core-containment premise still owed in the even-degree argument.
No ambient-recognition statement is inferred from that conditional result.
Source: Aschbacher–Smith §5.3.3 and §5.3.7, printed pp.659–660, applied
in Chapter12, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
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

/-- Both original full-normalizer intersection bounds, including q=4. -/
theorem rankOne_global_linear_local_centralizers
    (i : Fin 2) (z : G) (hz : z ∈ centerIn (Global.sourceS L H)) (hne : z ≠ 1) :
    (![L,residual H] i) ⊓ centralizer ({z} : Set G) = Global.sourceS L H ∧
    centralizer ({z} : Set G) ⊓ normalizer (![L,residual H] i : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.linear_factor_centralizer hi hH hp F hm hF he hmax i z hz hne,
    d.linear_normalizer_centralizer_le_inter hi hH hp F hm hF he hmax i z hz hne⟩

/-- The generic local elimination requires only the stated core containment. -/
theorem rankOne_global_linear_centralizer_of_core_le
    (z : G) (hz : orderOf z = 2) (hzS : z ∈ centerIn (Global.sourceS L H))
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ Global.sourceS L H) :
    centralizer ({z} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.linear_centralizer_le_inter_of_core_le (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax z hz hzS hzT hR

/-- Transitivity uses the whole original normalizer intersection. -/
theorem rankOne_global_linear_center_transitive
    (z w : G) (hz : z ∈ centerIn (Global.sourceS L H)) (hw : w ∈ centerIn (Global.sourceS L H))
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) :
    ∃ g ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G), g * z * g⁻¹ = w :=
  d.linear_center_transitive (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax z w hz hw hz1 hw1

/-- The original central line contains a Sylow-central involution. -/
theorem rankOne_global_linear_exists_sylow_central_involution :
    ∃ z : G, z ∈ centerIn (Global.sourceS L H) ∧ orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) :=
  d.linear_exists_sylow_central_involution (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
