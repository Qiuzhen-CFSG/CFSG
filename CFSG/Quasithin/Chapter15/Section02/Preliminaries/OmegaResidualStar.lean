module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaResidual
public import CFSG.Quasithin.Chapter15.Section01.ChosenCentralizerPlacement
public import Theory.GroupTheory.PCoreCommutator
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# The literal star centralization for the Omega residual

The chosen-module centralizer is normal in M and is contained in M∩M_c.
Its commutator with O₂(M∩M_c) lies in O₂(M). The same bound holds for the
M-normal closure and hence its two-residual, which is precisely the source
Y in the Omega row. Passing to M/O₂(M) proves 15.2.3(5), without a retained
star-commutator premise or a change of residual.

Source: Aschbacher--Smith, 14.1.17(3) and 15.2.3(5), printed pp.980,1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem kernel_intersection_core_commutator
    {M Mc V : Subgroup G} (hn : M ≤ normalizer (V : Set G))
    (hC : M ⊓ centralizer (V : Set G) ≤ Mc) :
    ⁅(actionHom M V hn).ker, ((M ⊓ Mc).pCoreIn 2).subgroupOf M⁆ ≤ pCore 2 M := by
  let H := (M ⊓ Mc).subgroupOf M
  have hCH : (actionHom M V hn).ker ≤ H := by
    intro x hx
    rw [actionHom_ker] at hx
    exact ⟨x.property, hC ⟨x.property, hx⟩⟩
  have he : H.pCoreIn 2 = ((M ⊓ Mc).pCoreIn 2).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_pCoreIn_of_injective 2 H M.subtype M.subtype_injective,
      show H.map M.subtype = M ⊓ Mc from map_subgroupOf_eq_of_le inf_le_left,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans inf_le_left)]
  exact he ▸ commutator_pCoreIn_le_of_normal (p := 2) (actionHom M V hn).ker H hCH

/-- Original 15.2.3(5) in the literal M/O₂(M), for the chosen Omega module. -/
theorem source_omega_lemma_15_2_3_5 (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized)) :
    let q := QuotientGroup.mk' (pCore 2 M)
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map q ⊔ (Y.subgroupOf M).map q ≤
      centralizer (((M ⊓ centralizer (V : Set G)).subgroupOf M).map q : Set (M ⧸ pCore 2 M)) := by
  let f := actionHom M V hV.normalized
  let R := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let q := QuotientGroup.mk' (pCore 2 M)
  have hC : M ⊓ centralizer (V : Set G) ≤ Mc :=
    inf_le_right.trans (hV.centralizer_le_partner T hu)
  have hcomm : ⁅f.ker, R⁆ ≤ pCore 2 M :=
    kernel_intersection_core_commutator hV.normalized hC
  have he : Y.subgroupOf M = twoResidualAmbient (normalClosure (R : Set M)) := by
    have hh := source_omega_caseIIResidual_image T hTM hV.normalized ho
      (MonoidHom.id M) Function.surjective_id (Mc := Mc)
    simpa only [Subgroup.map_id] using hh
  have hcommY : ⁅f.ker, Y.subgroupOf M⁆ ≤ pCore 2 M := by
    rw [he]
    exact (commutator_mono le_rfl (map_subtype_le _)).trans
      (commutator_normalClosure_le_of_normal f.ker R (pCore 2 M) hcomm)
  have hCeq : (M ⊓ centralizer (V : Set G)).subgroupOf M = f.ker := by
    rw [show f = actionHom M V hV.normalized from rfl, actionHom_ker]
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
  have lift (X : Subgroup M) (hX : ⁅f.ker, X⁆ ≤ pCore 2 M) :
      X.map q ≤ centralizer (f.ker.map q : Set (M ⧸ pCore 2 M)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hX
  change R.map q ⊔ (Y.subgroupOf M).map q ≤
    centralizer (((M ⊓ centralizer (V : Set G)).subgroupOf M).map q : Set (M ⧸ pCore 2 M))
  rw [hCeq]
  exact sup_le (lift R hcomm) (lift (Y.subgroupOf M) hcommY)

end CFSG.Quasithin.Chapter15.Section02
