module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaChosenComplete
public import CFSG.Quasithin.Chapter15.Section01.MinimalParabolicSource
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import CFSG.Quasithin.ChapterE.Section02.Structure.WreathRank

/-!
# The direct Omega obstruction to the symmetric-five wreath case

The prepared chosen module centralizes the original intersection residual
O²(H ∩ M). Taking the two-residual preserves three-rank, so the completed
Omega centralizer bound gives m₃(H ∩ M) ≤ 1. Original15.1.9(7) identifies
this same intersection with the unique maximal above the intrinsic Sylow
subgroup of H. In the S₅ wreath C₂ quotient, the action on 25 points gives
the opposite bound. This proves the Omega branch of15.2.4 directly, without
constructing the stronger elementary-nine star-image isomorphism.

Source: Aschbacher--Smith15.1.9(4,7),15.2.3--4, pp.1088--1089,1104--1106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The original intersection has three-rank at most one in the Omega case. -/
theorem source_omega_chosen_HStar_intersection_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    primeRank 3 (H ⊓ M : Subgroup G) ≤ 1 := by
  let X := (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype
  have hXC : X ≤ M ⊓ centralizer (V : Set G) :=
    le_inf ((map_subtype_le _).trans inf_le_right) (hV.intersection_residual H hH)
  have hX : primeRank 3 X ≤ 1 :=
    (primeRank_mono 3 hXC).trans
      (source_omega_chosen_residual_complete hG T hempty hM hJ hu hmany hV ho).centralizer_rank
  have he := primeRank_equiv 3 ((pResidual 2 (H ⊓ M : Subgroup G)).equivMapOfInjective
    (H ⊓ M).subtype (H ⊓ M).subtype_injective)
  have hr := ResidualCentralizerRank.primeRank_residual
    (G := (H ⊓ M : Subgroup G)) (by decide : Nat.Coprime 2 3)
  exact hr.symm.trans_le (he.trans_le hX)

/-- The same bound on the intrinsic maximal subgroup of the original H-star local. -/
theorem source_omega_chosen_HStar_minimalParabolic_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let S := T.subtype hH.1.1.2
    ∃ hP : ChapterB.IsMinimalParabolicOver S ⊤,
      primeRank 3 (ChapterB.minimalParabolicMax S hP) ≤ 1 := by
  obtain ⟨_, hP, hmax, _, _⟩ := source_centralizing_minimalParabolic hG T hM hJ H hH
  refine ⟨hP, ?_⟩
  have he := ChapterB.minimalParabolicMax_unique (T.subtype hH.1.1.2) hP hmax
    (show ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) ≤ (H ⊓ M).subgroupOf H from
      fun x hx => ⟨x.property, hM.1.2 hx⟩)
  rw [← he]
  exact (primeRank_equiv 3 (subgroupOfEquivOfLe (show (H ⊓ M : Subgroup G) ≤ H from
    inf_le_left))).trans_le
      (source_omega_chosen_HStar_intersection_rank hG T hempty hM hJ hu hmany hV ho hH)

/-- Original15.2.4 in the Omega row, with no extra model or rank premises. -/
theorem source_omega_chosen_HStar_not_symmetricFive_wreath
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) := by
  rintro ⟨e⟩
  obtain ⟨hP, hupper⟩ := source_omega_chosen_HStar_minimalParabolic_rank
    hG T hempty hM hJ hu hmany hV ho hH
  have hlower := ChapterE.Structure.minimalParabolicMax_three_rank_of_symmetricFive_wreath
    (T.subtype hH.1.1.2) hP e
  omega


end CFSG.Quasithin.Chapter15.Section02
