module
public import CFSG.Quasithin.Chapter10.SourceSetup
public import CFSG.Quasithin.Chapter3.Defs
public import Theory.SpecificGroups.PSL3Two.PairOvergroups

/-!
# Proper Sylow overgroups of the original linear-three local join

Transport the exchanged-pair calculation to the literal L₀T and its full
two-core. The original maximal-two-local uniqueness theorem makes H∩L₀T
proper for every H* group, so the source consumer supplies the required
properness without a new hypothesis.

Source: Aschbacher--Smith,10.2.3(ii), printed p.745, using10.1.1 and3.2.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.LinearThree
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The proper-overgroup theorem applied to the literal original local join. -/
theorem source_proper_overgroup_six
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hP : P < localJoin T L) :
    IsPGroup 6 P := by
  let J := localJoin T L
  have hLJ : L ≤ J := (le_componentOrbit L T).trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  let S := T.subtype hTJ
  let A := L.subgroupOf J
  have hA : A.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  let a := subgroupOfEquivOfLe hLJ
  let eA := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  have hgen : A ⊔ (S : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [← subgroupOf_sup hLJ hTJ]
    have hh : L ⊔ (T : Subgroup G) = J := (componentOrbit_sup L (T : Subgroup G)).symm
    rw [hh,subgroupOf_self]
  have hi : (normalizer (A : Set J)).index = 2 := by
    change (normalizer (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔
      (T : Subgroup G)) : Set (componentOrbit L (T : Subgroup G) ⊔
      (T : Subgroup G) : Subgroup G))).index = 2
    rw [componentOrbit_sup]
    exact source_nonnormal_normalizer_index D.simpleQTKE D.maximal.1 hn
  have hSP : (S : Subgroup J) ≤ P.subgroupOf J := fun _ hx => hTP hx
  have hPne : P.subgroupOf J ≠ ⊤ := fun he => hP.not_ge (subgroupOf_eq_top.mp he)
  exact (Matrix.PSL3Two.component_pair_proper_overgroup_six S A hA eA hi hgen (P.subgroupOf J)
    hSP hPne).of_equiv (subgroupOfEquivOfLe hP.le)

/-- Original uniqueness makes the intersection with an H* group proper. -/
theorem source_hstar_inf_localJoin_lt
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ⊓ localJoin T L < localJoin T L := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  apply lt_of_le_of_ne inf_le_right
  intro he
  have hjoinH : localJoin T L ≤ H := by rw [← he]; exact inf_le_left
  exact hH.1.2 (hHN.trans (normalizer_le_of_unique_maximalTwoLocal
    (D.lemma_3_2_3_uniqueness hu).2.2 (isPGroup_pCoreIn 2 H) hH.1.1.1
    (hjoinH.trans hHN)))

end CFSG.Quasithin.Chapter10.CentralHall.LinearThree
