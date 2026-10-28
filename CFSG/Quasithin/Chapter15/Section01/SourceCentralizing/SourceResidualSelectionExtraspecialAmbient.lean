module

public import CFSG.Quasithin.Chapter15.Section01.CaseI.Setup
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed.ThompsonCenterNormalizer

/-!
# The original fixed-subgroup normalizer under the maximal-overgroup pair

The original Thompson-center centralizer escapes the selected local and
normalizes the literal chosen fixed subgroup. Its full normalizer is a
two-local containing the original Sylow subgroup. If the only maximal
two-locals over that Sylow subgroup are the selected local and its partner,
the fixed-subgroup normalizer therefore lies in the partner.

This consequence does not use the global residual conclusion of 15.1.14.
It applies to any prepared chosen source module, including the full Nine
and extraspecial rows when their maximal-overgroup pair is established.

Source: Aschbacher--Smith 15.1.13(1) and 15.1.14(2), printed pp.1090--1091.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original maximal-overgroup pair places the normalizer of the same
chosen Thompson fixed subgroup in the partner, without a residual premise. -/
theorem PreparedChosenModule.thompsonFixed_normalizer_le_of_maximal_overgroups_pair
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc}) :
    normalizer (thompsonFixed T V : Set G) ≤ Mc := by
  let := h.elementary
  have hsetup := h.caseI_thompson_setup hG T hempty hM hmany hJ
  have hTJ : (T : Subgroup G) ≤
      normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (ChapterB.thompsonJ (T : Subgroup G) 1).map (MulAut.conj t).toMonoidHom = _
    rw [← ChapterB.thompsonJ_map_equiv]
    exact congrArg (fun S => ChapterB.thompsonJ S 1)
      (mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht))
  have hTN : (T : Subgroup G) ≤ normalizer (thompsonFixed T V : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      (hTJ.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  have hlocal : IsTwoLocal (normalizer (thompsonFixed T V : Set G)) :=
    ⟨thompsonFixed T V, hsetup.1,
      (IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left, rfl⟩
  obtain ⟨N, hEN, hN⟩ := Finite.exists_le_maximal hlocal
  have hNmem : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) :=
    ⟨hN, hTN.trans hEN⟩
  rw [htwo, Set.mem_insert_iff, Set.mem_singleton_iff] at hNmem
  rcases hNmem with rfl | rfl
  · exact (hsetup.2.2.2.1 ((Subgroup.centralizer_le_normalizer _).trans
      ((h.thompsonCenter_normalizer_le_fixed_normalizer hG T hM hJ).trans hEN))).elim
  · exact hEN

/-- Every subgroup of the original fixed subgroup gives a marked centralizer
whose Sylow supplement has the unique maximal two-local overgroup `Mc`.
The original Thompson-center escape supplies the exclusion of `M`. -/
theorem PreparedChosenModule.marked_centralizer_uniqueness_of_maximal_overgroups_pair
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (htwo : maximalTwoLocalOvergroups (T : Subgroup G) = {M, Mc})
    (hZ : Z1 ≤ thompsonFixed T V) :
    ¬ centralizer (Z1 : Set G) ⊓ Mc ≤ M ∧
      maximalTwoLocalOvergroups
        ((centralizer (Z1 : Set G) ⊓ Mc) ⊔ (T : Subgroup G)) = {Mc} := by
  have hNM := h.thompsonFixed_normalizer_le_of_maximal_overgroups_pair
    hG T hempty hM hmany hJ htwo
  have hOmega : centralizer
      (omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) : Set G) ≤
        centralizer (Z1 : Set G) ⊓ Mc :=
    le_inf (centralizer_le (hZ.trans (h.thompsonFixed_le_omega T hM)))
      ((centralizer_le (h.thompsonFixed_le_omega T hM)).trans
        ((Subgroup.centralizer_le_normalizer _).trans hNM))
  have hescape : ¬ centralizer (Z1 : Set G) ⊓ Mc ≤ M := fun hm =>
    (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).1
      (hOmega.trans hm)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := by
    rw [htwo]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton Mc)
  refine ⟨hescape, ?_⟩
  ext N
  constructor
  · rintro ⟨hN, hle⟩
    have hNmem : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) :=
      ⟨hN, le_sup_right.trans hle⟩
    rw [htwo, Set.mem_insert_iff, Set.mem_singleton_iff] at hNmem
    rcases hNmem with rfl | rfl
    · exact (hescape (le_sup_left.trans hle)).elim
    · exact Set.mem_singleton _
  · intro hN
    obtain rfl := Set.mem_singleton_iff.mp hN
    exact ⟨hMc.1, sup_le inf_le_right hMc.2⟩

end CFSG.Quasithin.Chapter15.Section01
