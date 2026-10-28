module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OrbitUniqueness

/-!
# The literal starred preimage in the Omega Case-II row

In the natural Ω₄⁺(2) row, the starred core is the entire conjugation
image on the chosen module. Its preimage M₀ is therefore M. This
identifies the earlier 15.1.5(1) orbit with the already prepared orbit
under M and removes that extra premise from the YT uniqueness consumer.
The chosen module may be V(M) or the proper support from 15.1.4.

Source: Aschbacher--Smith, 15.1.4--5, printed p.1087; 15.2.1(3),
15.2.2 and 15.2.3(3), printed pp.1104--1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G]

/-- The actual preimage M₀ of J-hat on the chosen V, as in 15.1.4. -/
noncomputable abbrev chosenStarredPreimage (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) : Subgroup G :=
  ((Jhat (imageRepresentation M V hn)).comap (actionHom M V hn).rangeRestrict).map M.subtype

/-- The Omega row identifies the original starred preimage with M. -/
theorem chosenStarredPreimage_eq_of_omega
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    chosenStarredPreimage M V hn = M := by
  apply le_antisymm (map_subtype_le _)
  intro m hm
  refine ⟨⟨m, hm⟩, ?_, rfl⟩
  have hall : ∀ a : internalActionImage M V hn, a ∈ Jhat (imageRepresentation M V hn) := by
    intro a
    rw [ho.1]
    exact mem_top a
  exact hall _

/-- The original 15.1.5(1) orbit identity is fully supplied in the Omega row. -/
theorem source_chosen_starred_span_of_omega
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized)) :
    V = conjugateSpanBy (centralInvolutions T ⊓ V)
      (chosenStarredPreimage M V hV.normalized) := by
  rw [chosenStarredPreimage_eq_of_omega M V hV.normalized ho]
  exact hV.seed_span

/-- Apply the Omega row to the literal residual YT in 15.2.3(3).
Only its preceding residual image conclusion remains to be supplied. -/
theorem source_omega_residual_sylow_unique [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V Y : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hV : PreparedChosenModule T M V) (hYM : Y ≤ M)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (himage : ((chosenStarredPreimage M V hV.normalized).subgroupOf M).map
      (actionHom M V hV.normalized) ≤
      ((Y ⊔ (T : Subgroup G)).subgroupOf M).map (actionHom M V hV.normalized)) :
    maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) = {M} := by
  exact source_residual_sylow_unique_of_action_image hG T hempty hM hJ hV hYM
    (map_subtype_le _) (source_chosen_starred_span_of_omega T hV ho) himage

/-- The original Y in 15.2.3, retaining its Rc and its O²(M₀)T orbit. -/
noncomputable abbrev caseIIResidual (T : Sylow 2 G) (M M₀ Mc : Subgroup G) : Subgroup G :=
  twoResidualAmbient (conjugateSpanBy ((M ⊓ Mc).pCoreIn 2)
    (twoResidualAmbient M₀ ⊔ (T : Subgroup G)))

private theorem caseIIResidual_le (T : Sylow 2 G) {M M₀ Mc : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hM₀M : M₀ ≤ M) :
    caseIIResidual T M M₀ Mc ≤ M := by
  apply (map_subtype_le _).trans
  apply conjugateSpanBy_le ((pCoreIn_le 2 _).trans inf_le_left)
  exact (sup_le ((map_subtype_le _).trans hM₀M) hTM).trans M.le_normalizer

/-- The literal Omega application of 15.2.3(3). Its Y is constructed from
Rc = O₂(M ∩ Mc) and the exact O²(M₀)T orbit, so no containment or orbit
identity for Y is an additional premise. The prior residual image calculation
is the only retained 15.2.3 input. -/
theorem source_omega_lemma_15_2_3_3 [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (himage : let M₀ := chosenStarredPreimage M V hV.normalized
      let Y := caseIIResidual T M M₀ Mc
      (M₀.subgroupOf M).map (actionHom M V hV.normalized) ≤
        ((Y ⊔ (T : Subgroup G)).subgroupOf M).map (actionHom M V hV.normalized)) :
    maximalTwoLocalOvergroups
      (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
        (T : Subgroup G)) = {M} := by
  exact source_omega_residual_sylow_unique hG T hempty hM hJ hV
    (caseIIResidual_le T hM.1.2 (map_subtype_le _)) ho himage

end CFSG.Quasithin.Chapter15.Section02
