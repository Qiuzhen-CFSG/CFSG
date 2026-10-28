module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.CounterexampleThompsonResidual.ProperImageTwo.FixedPlane
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.CounterexampleThompsonResidual.ProperImageTwo.CoreContainment
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonProper
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed.Normalization
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaChosenComplete

/-!
# The local data on the exceptional proper Thompson support

Transfer the complete original proper-support witness to its literal mapped
subgroup. Its natural Omega coordinates give dimension four, so an order-two
Thompson action fixes a subgroup of order four. The independently proved
15.2.3 theorem applies to the same prepared support and its original action
and quotient maps, including when the support is proper.

Failure of global normalization supplies a moving minimal parabolic whose
two-core contains the original fixed plane but does not centralize it. The
same residual centralizes the core's central omega. These conclusions retain
the local residual structure for studying original 15.1.14. Global
normalization by `C_G(Ω₁Z(T))` remains unproved here.

Source: Aschbacher--Smith, 15.1.13--14 and 15.2.3, printed pp.1090--1091
and 1104--1106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Apply the fixed-plane calculation to the actual mapped proper support. -/
theorem source_proper_image_two_fixed_card
    (T : Sylow 2 G) {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (U : Submodule (ZMod 2) (Additive V))
    (hU : SourceCases.Proper T M Mc V (imageRepresentation M V hn) U) :
    let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
    ∀ hp : PreparedChosenModule T M W,
      Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M W hp.normalized).rangeRestrict) = 2 →
      Nat.card (thompsonFixed T W) = 4 := by
  intro W hp htwo
  let := hp.elementary
  exact hp.thompsonFixed_card_of_image_two T hTM
    (hU.chosen_omega T M Mc V hn U hp.normalized).2.2.1 htwo

/-- The exceptional proper branch has both the complete local residual theorem
and a four-element Thompson fixed subgroup, on the original chosen action. -/
theorem source_proper_image_two_fixed_plane_and_omega_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1, hM.1.2⟩
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (_hU : SourceCases.Proper T M Mc (localModule T M)
        (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U),
    let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map (localModule T M).subtype
    ∀ hp : PreparedChosenModule T M W,
      Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M W hp.normalized).rangeRestrict) = 2 →
      letI := hp.elementary
      Nat.card (thompsonFixed T W) = 4 ∧
        Section02.OmegaResidualConclusions T M Mc W hp.normalized := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1, hM.1.2⟩
  intro U hU W hp htwo
  let := hp.elementary
  exact ⟨source_proper_image_two_fixed_card T (V := localModule T M) hM.1.2
    (le_normalizer_conjugateSpanBy _ _) U hU hp htwo,
    Section02.source_omega_chosen_residual_complete hG T hempty hM hJ hu hmany hp
      (hU.chosen_omega T M Mc (localModule T M)
        (le_normalizer_conjugateSpanBy _ _) U hp.normalized)⟩

/-- Apply core containment to the actual proper support and the original moving
parabolic. Noncentrality of the four in its core is the remaining obstruction. -/
theorem source_proper_image_two_moving_core_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1, hM.1.2⟩
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (_hU : SourceCases.Proper T M Mc (localModule T M)
        (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) U),
    let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map (localModule T M).subtype
    ∀ hp : PreparedChosenModule T M W,
      Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M W hp.normalized).rangeRestrict) = 2 →
      ¬ centralizer (centralInvolutions T : Set G) ≤ normalizer (thompsonFixed T W : Set G) →
      Nat.card (thompsonFixed T W) = 4 ∧
      ∃ P : Subgroup G, P ≤ centralizer (centralInvolutions T : Set G) ∧
        P ∈ Chapter1.HOver G (T : Set G) ∧ ChapterB.IsMinimalParabolicOver T P ∧
        IsSQTK KnownSimple.IsKnownSimple P ∧ generalizedFitting P = pCore 2 P ∧
        ¬ P ≤ M ∧ ¬ IsMulCommutative (pCore 2 P) ∧
        pResidual 2 P ≤ centralizer (omegaCenterIn (pCore 2 P) : Set P) ∧
        (∀ A : Subgroup P, IsPReduced 2 A → centralizer (A : Set P) = ⊤) ∧
        ¬ (pResidual 2 P).map P.subtype ≤ centralizer (thompsonFixed T W : Set G) ∧
        thompsonFixed T W ≤ P.pCoreIn 2 ∧
        ¬ P.pCoreIn 2 ≤ centralizer (thompsonFixed T W : Set G) ∧
        ¬ P.pCoreIn 2 ≤ ChapterB.thompsonJ (T : Subgroup G) 1 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1, hM.1.2⟩
  intro U hU W hp htwo hn
  have hfour := source_proper_image_two_fixed_card T (V := localModule T M) hM.1.2
    (le_normalizer_conjugateSpanBy _ _) U hU hp htwo
  have hres := mt (hp.thompsonFixed_residual_iff_normalizes hG T hM hJ).mp hn
  obtain ⟨P, hPC, hPH, hpar, hSQ, hF, hPM, hna, hω, hred, hmove, hQJ, _⟩ :=
    hp.thompsonFixed_moving_parabolic_core_obstruction hG T hempty hM hJ hres
  exact ⟨hfour, P, hPC, hPH, hpar, hSQ, hF, hPM, hna, hω, hred, hmove,
    hp.thompsonFixed_four_le_core hG T hM hfour hPH hPC,
    hp.moving_fixed_four_core_not_centralizes hG T hempty hM hJ hfour hPH hPC hpar hPM hmove,
    hQJ⟩

end CFSG.Quasithin.Chapter15.Section01
