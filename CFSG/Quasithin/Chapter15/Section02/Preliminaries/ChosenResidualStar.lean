module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaUniqueness
public import CFSG.Quasithin.Chapter15.Section01.ChosenCoreIntersection
public import Theory.GroupTheory.PCoreCommutator
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Star centralization for every prepared Case II module

The chosen centralizer lies in M ∩ M_c. Its commutator with the
intersection two-core lies in O₂(M), hence so does its commutator with
any subgroup of the M-normal closure. The literal Case II residual has
this containment even when its conjugating group O²(M₀)T is proper.

We also retain that relative conjugating group when transporting the
residual to an action or quotient, and use the prepared module's reduced
structure to factor its action through M/O₂(M).

Source: Aschbacher--Smith14.1.17(3),15.1.5 and15.2.3(5), pp.980,1087,1105.
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

/-- Original15.2.3(5), for the literal residual of every prepared chosen module. -/
theorem source_chosen_lemma_15_2_3_5 (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V) :
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
  have hYM : Y.subgroupOf M ≤ normalClosure (R : Set M) := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy _ _
      ((pCoreIn_le 2 _).trans inf_le_left)]
    apply comap_mono
    exact (map_subtype_le _).trans (conjugateSpanBy_mono le_rfl
      (sup_le ((map_subtype_le _).trans (map_subtype_le _)) hTM))
  have hcommY : ⁅f.ker, Y.subgroupOf M⁆ ≤ pCore 2 M :=
    (commutator_mono le_rfl hYM).trans
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

omit [Finite G] in
/-- Containment of the literal source residual, for every starred preimage. -/
theorem source_caseIIResidual_le (T : Sylow 2 G) {M M₀ Mc : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hM₀M : M₀ ≤ M) :
    caseIIResidual T M M₀ Mc ≤ M := by
  apply (map_subtype_le _).trans
  apply conjugateSpanBy_le ((pCoreIn_le 2 _).trans inf_le_left)
  exact (sup_le ((map_subtype_le _).trans hM₀M) hTM).trans M.le_normalizer

/-- The residual image keeps the original relative conjugating group. -/
theorem source_caseIIResidual_image {D : Type*} [Group D] [Finite D]
    (T : Sylow 2 G) {M M₀ Mc : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hM₀M : M₀ ≤ M) (f : M →* D) :
    ((caseIIResidual T M M₀ Mc).subgroupOf M).map f =
      twoResidualAmbient (conjugateSpanBy
        ((((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f)
        (((twoResidualAmbient M₀ ⊔ (T : Subgroup G)).subgroupOf M).map f)) := by
  let R := (M ⊓ Mc).pCoreIn 2
  let B := twoResidualAmbient M₀ ⊔ (T : Subgroup G)
  have hRM : R ≤ M := (pCoreIn_le 2 _).trans inf_le_left
  have hBM : B ≤ M := sup_le ((map_subtype_le _).trans hM₀M) hTM
  have he : (conjugateSpanBy (R.subgroupOf M) (B.subgroupOf M)).map M.subtype =
      conjugateSpanBy R B := by
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le hRM, map_subgroupOf_eq_of_le hBM]
  change ((twoResidualAmbient (conjugateSpanBy R B)).subgroupOf M).map f = _
  rw [← map_twoResidualAmbient_of_subgroup_image _ M.subtype _ he,
    ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
  exact map_twoResidualAmbient_of_subgroup_image _ f _ (map_conjugateSpanBy _ _ f)

/-- The prepared chosen module kills the original local two-core. -/
theorem source_chosen_core_le_kernel (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hV : PreparedChosenModule T M V) :
    pCore 2 M ≤ (actionHom M V hV.normalized).ker := by
  rw [actionHom_ker]
  have hi := le_centralizer_iff.mp (hV.reduced T hTM).le_centralizer_pCore
  intro x hx v hv
  exact congrArg M.subtype (hi hx ⟨v,hV.le_selected hv⟩ hv)

end CFSG.Quasithin.Chapter15.Section02
