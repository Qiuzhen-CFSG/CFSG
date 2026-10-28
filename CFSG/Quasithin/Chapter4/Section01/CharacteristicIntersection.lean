module
public import CFSG.Quasithin.Chapter4.Section01.RadicalBounds
public import CFSG.Quasithin.Chapter1.Section01Overgroups
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
import Mathlib.Tactic
/-!
# Characteristic two for the actual pushing-up intersection

For a maximal outside H, the two-core bounds make the centralizer of
O2(H intersect M) in O2(M) lie in H. The original even-characteristic
condition and1.1.4(5) therefore make H intersect M characteristic two.
An arbitrary outside H is handled inside a maximal overgroup: its core
bounds transport the self-centralizer inequality downward. This proves
the original generalized-Fitting conclusion, not only a reformulation
for maximal two-locals.
Source: Aschbacher--Smith,4.1.4(6), printed p.607.
-/

public section
namespace CFSG.Quasithin.Chapter4
open Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem intersection_mem_He_of_maximal {K : GroupClass} {T : Sylow 2 G}
    {M X Mminus I H : Subgroup G} (hyp : Hypothesis411 K T M X)
    (hminus : Mminus ∈ sigma M X) (hI : I ∈ muStar M X Mminus)
    (hH : IsMaximalTwoLocal H) (hIH : I ≤ H) (hout : ¬ H ≤ M) :
    H ⊓ M ∈ Chapter1.He G := by
  have hcores := (lemma_4_1_4_5 hyp hminus hI
    (Chapter1.mem_H_of_isTwoLocal hH.1) hIH hout).2.2.1
  have hR : I.pCoreIn 2 ≤ H ⊓ M :=
    (pCoreIn_le 2 I).trans (le_inf hIH (hI.1.1.1.trans hminus.1))
  have hne : H ⊓ M ≠ ⊥ := fun he => hI.1.1.2.2.2 (bot_unique (he ▸ hR))
  apply Chapter1.lemma_1_1_4_5 T (hyp.simpleQTKE.evenCharacteristic T)
    hyp.maximal hyp.sylow_le hne inf_le_right
  intro x hx
  exact ⟨centralizer_core_le_of_maximal hH (centralizer_le hcores hx.2),
    pCoreIn_le 2 M hx.1⟩

/-- The actual intersection H∩M is characteristic two for every outside
H with nontrivial core, not only for maximal two-locals. -/
theorem intersection_mem_He_of_muStar {K : GroupClass} {T : Sylow 2 G}
    {M X Mminus I H : Subgroup G} (hyp : Hypothesis411 K T M X)
    (hminus : Mminus ∈ sigma M X) (hI : I ∈ muStar M X Mminus)
    (hH : H ∈ Chapter1.H G) (hIH : I ≤ H) (hout : ¬ H ≤ M) :
    H ⊓ M ∈ Chapter1.He G := by
  have hne : pCore 2 H ≠ ⊥ := by
    intro he
    exact hH (by simp only [pCoreIn,he,Subgroup.map_bot])
  obtain ⟨H1,hH1,hHH1⟩ :=
    Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hne
  have hIH1 := hIH.trans hHH1
  have hout1 : ¬ H1 ≤ M := fun hm => hout (hHH1.trans hm)
  have hHe := intersection_mem_He_of_maximal hyp hminus hI hH1 hIH1 hout1
  have hcore := (lemma_4_1_4_5 hyp hminus hI
    (Chapter1.mem_H_of_isTwoLocal hH1.1) hIH1 hout1).2.2.2
  have hR : I.pCoreIn 2 ≤ H ⊓ M :=
    (pCoreIn_le 2 I).trans (le_inf hIH (hI.1.1.1.trans hminus.1))
  have hAA : H ⊓ M ≤ H1 ⊓ M := inf_le_inf_right _ hHH1
  have hc : (H1 ⊓ M).pCoreIn 2 ≤ (H ⊓ M).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) (hcore.trans hR)
      (hAA.trans ((H1 ⊓ M).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))
  intro x hx
  exact hc (hHe ⟨hAA hx.1,centralizer_le hc hx.2⟩)

/-- Source4.1.4(6), in its original generalized-Fitting form. -/
theorem lemma_4_1_4_6 {K : GroupClass} {T : Sylow 2 G}
    {M X Mminus I H : Subgroup G} (hyp : Hypothesis411 K T M X)
    (hminus : Mminus ∈ sigma M X) (hI : I ∈ muStar M X Mminus)
    (hH : H ∈ Chapter1.H G) (hIH : I ≤ H) (hout : ¬ H ≤ M) :
    Theory.GroupTheory.generalizedFitting (H ⊓ M : Subgroup G) =
      pCore 2 (H ⊓ M : Subgroup G) :=
  Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp (intersection_mem_He_of_muStar hyp hminus hI hH hIH hout))
end CFSG.Quasithin.Chapter4
