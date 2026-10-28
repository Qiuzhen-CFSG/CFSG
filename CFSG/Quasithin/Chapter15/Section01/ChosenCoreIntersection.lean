module
public import CFSG.Quasithin.Chapter15.Section01.ChosenCentralizerPlacement
public import Theory.GroupTheory.PCoreCommutator

/-!
# The chosen module and the original intersection core

Generation from the original Sylow-central seed makes every prepared chosen
module reduced in M, including the proper moved four-space. Its normal
centralizer is contained in M ∩ M_c. Restricting normal two-cores therefore
identifies C_{O₂(M ∩ M_c)}(V) with O₂(M).

Consequently the nontriviality premise in the Case II action is exactly the
original intersection-core growth statement, with the actual chosen module
and original ambient subgroups. The exceptional source proof of that growth
is separate; no growth conclusion is assumed here.

Source: Aschbacher--Smith 14.1.17(1),(5), printed p.980, and 15.1.5(1),
printed p.1087.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The literal chosen module is reduced in the original selected local. -/
theorem PreparedChosenModule.reduced
    (T : Sylow 2 G) {M V : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (h : PreparedChosenModule T M V) : IsPReduced 2 (V.subgroupOf M) := by
  let := h.elementary
  apply reduced_of_sylow_central_seed T M V (centralInvolutions T ⊓ V)
    hTM h.le_selected h.normalized inf_le_right ?_ h.seed_span
  intro z hz s hs
  exact centralInvolutions_le_centralizer_sylow T hz.1 s hs

/-- The original intersection core has precisely the local core as its action kernel. -/
theorem PreparedChosenModule.intersection_core_centralizer
    (T : Sylow 2 G) {M Mc V : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) :
    (M ⊓ Mc).pCoreIn 2 ⊓ centralizer (V : Set G) = M.pCoreIn 2 := by
  let C := (centralizer (V : Set G)).subgroupOf M
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (h.normalized.trans (normalizer_le_normalizer_centralizer _))
  have hred := h.reduced T hTM
  have hQK : pCore 2 M ≤ C := by
    have hi := le_centralizer_iff.mp hred.le_centralizer_pCore
    intro x hx v hv
    exact congrArg M.subtype (hi hx ⟨v,h.le_selected hv⟩ hv)
  have hCI : C.map M.subtype ≤ M ⊓ Mc := by
    rw [show C = (centralizer (V : Set G)).subgroupOf M from rfl,subgroupOf_map_subtype]
    exact le_inf inf_le_right (inf_le_left.trans (h.centralizer_le_partner T hu))
  have hCcore : C.pCoreIn 2 = pCore 2 M := by
    rw [pCoreIn,pCore_eq_comap_of_normal,map_comap_eq,range_subtype,inf_eq_right.mpr hQK]
  have hQR : M.pCoreIn 2 ≤ (M ⊓ Mc).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) ((map_mono hQK).trans hCI)
      (inf_le_left.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))
  have hQC : M.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (map_mono hQK).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)
  apply le_antisymm
  · have hi := inf_pCoreIn_le_of_le 2 hCI
    rw [←map_pCoreIn_of_injective 2 C M.subtype M.subtype_injective,hCcore] at hi
    apply le_trans ?_ hi
    refine le_inf ?_ inf_le_left
    rw [show C = (centralizer (V : Set G)).subgroupOf M from rfl,subgroupOf_map_subtype]
    exact le_inf inf_le_right (inf_le_left.trans ((pCoreIn_le 2 _).trans inf_le_left))
  · exact le_inf hQR hQC

/-- The Case II noncentrality input is equivalent to original core growth. -/
theorem PreparedChosenModule.intersection_core_noncentral_iff
    (T : Sylow 2 G) {M Mc V : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) :
    (¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) ↔
      (M ⊓ Mc).pCoreIn 2 ≠ M.pCoreIn 2 := by
  have he := h.intersection_core_centralizer T hTM hu
  constructor
  · intro hn hc
    apply hn
    rw [hc]
    exact he.ge.trans inf_le_right
  · intro hn hc
    apply hn
    simpa only [inf_eq_left.mpr hc] using he

end CFSG.Quasithin.Chapter15.Section01
