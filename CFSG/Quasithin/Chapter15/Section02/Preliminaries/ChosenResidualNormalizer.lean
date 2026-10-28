module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.ChosenResidualStar
public import Theory.GroupTheory.UniqueLocalResidualKernel
/-!
# The original centralizer and Sylow normalize the chosen residual join

Original15.2.3(5) puts [C_M(V),Y] inside O₂(M), hence inside Rc. Since
C_M(V) ≤ M∩Mc, it normalizes Rc. Recovering the two-perfect residual from
its two-group supplement therefore proves that C_M(V) normalizes Y.
The defining orbit construction gives the T-normalization directly.
Consequently C_M(V)T normalizes both Y and YRc.

In original15.2.4 the opposite Borel lies in X₁S ≤ C_M(V)T; this result
supplies its normalization of the literal L₀=YRc. It does not require
normality of Y in all of M or a particular source action case.
Source: Aschbacher--Smith15.2.3(5),15.2.4, printed pp.1105--1106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]
private theorem residual_notation (K : Subgroup G) :
    twoResidualAmbient K = (pResidual 2 K).map K.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN,n,hn⟩
    exact ⟨hN,IsPGroup.of_card hn⟩
  · rintro ⟨hN,hn⟩
    exact ⟨hN,IsPGroup.iff_card.mp hn⟩

/-- The actual C_M(V)T normalizes the chosen residual and its Rc supplement. -/
theorem source_chosen_centralizer_sylow_normalizes_residual (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let R := (M ⊓ Mc).pCoreIn 2
    (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) ≤ normalizer (Y ⊔ R : Subgroup G) := by
  let C := M ⊓ centralizer (V : Set G)
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let R := (M ⊓ Mc).pCoreIn 2
  let A := twoResidualAmbient (chosenStarredPreimage M V hV.normalized) ⊔ (T : Subgroup G)
  let K := conjugateSpanBy R A
  have hYR : Y = (pResidual 2 K).map K.subtype := residual_notation K
  have hYM : Y ≤ M := source_caseIIResidual_le T hTM (map_subtype_le _)
  have hCR : C ≤ normalizer (R : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans (hV.centralizer_le_partner T hu))).trans
      ((M ⊓ Mc).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (M ⊓ Mc) (pCore 2 ↑(M ⊓ Mc))))
  let q := QuotientGroup.mk' (pCore 2 M)
  have hcent : (Y.subgroupOf M).map q ≤ centralizer ((C.subgroupOf M).map q : Set (M ⧸ pCore 2 M)) :=
    le_sup_right.trans (source_chosen_lemma_15_2_3_5 T hTM hu hV)
  have hcommM : ⁅C.subgroupOf M,Y.subgroupOf M⁆ ≤ pCore 2 M := by
    rw [←show q.ker = pCore 2 M from QuotientGroup.ker_mk' _]
    apply (Subgroup.map_eq_bot_iff (f := q) _).mp
    rw [map_commutator,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcent
  have hcomm : ⁅C,Y⁆ ≤ R := by
    have hh := map_mono (f := M.subtype) hcommM
    rw [map_commutator,map_subgroupOf_eq_of_le (show C ≤ M from inf_le_left),
      map_subgroupOf_eq_of_le hYM] at hh
    exact hh.trans ((hV.intersection_core_centralizer T hTM hu).symm.le.trans inf_le_left)
  have hCY : C ≤ normalizer (Y : Set G) := by
    rw [hYR] at hcomm ⊢
    exact normalizes_residual_of_commutator_le_two C K K R K.le_normalizer
      (le_conjugateSpanBy R A) (isPGroup_pCoreIn 2 (M ⊓ Mc)) hCR hcomm
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := by
    rw [hYR]
    exact (show (T : Subgroup G) ≤ A from le_sup_right).trans
      ((le_normalizer_conjugateSpanBy R A).trans
        (normalizer_le_normalizer_characteristic_image K (pResidual 2 K)))
  have hTMc : (T : Subgroup G) ≤ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf hTM hTMc).trans ((M ⊓ Mc).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (M ⊓ Mc) (pCore 2 ↑(M ⊓ Mc))))
  have hN := sup_le hCY hTY
  exact ⟨hN,(le_inf hN (sup_le hCR hTR)).trans
    (normalizer_inf_normalizer_le_normalizer_sup Y R)⟩
/-- The actual H-star intersection residual puts Rc inside the two-core of XT. -/
theorem source_chosen_intersection_core_le_HStar_core (T : Sylow 2 G)
    {M Mc V H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let X := (pResidual 2 ↑(H ⊓ M)).map (H ⊓ M).subtype
    (M ⊓ Mc).pCoreIn 2 ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let X := (pResidual 2 ↑(H ⊓ M)).map (H ⊓ M).subtype
  let R := (M ⊓ Mc).pCoreIn 2
  have hTMc : (T : Subgroup G) ≤ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hRT : R ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf hTM hTMc))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (le_inf hTM hTMc)] using hh
  have hXI : X ≤ M ⊓ Mc := le_inf ((map_subtype_le _).trans inf_le_right)
    ((hV.intersection_residual H hH).trans (hV.centralizer_le_partner T hu))
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (M ⊓ Mc)) (hRT.trans le_sup_right)
  exact (sup_le hXI (le_inf hTM hTMc)).trans ((M ⊓ Mc).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (M ⊓ Mc) (pCore 2 ↑(M ⊓ Mc))))

end CFSG.Quasithin.Chapter15.Section02
