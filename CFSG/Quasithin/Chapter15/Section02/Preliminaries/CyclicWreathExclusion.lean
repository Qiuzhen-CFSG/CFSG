module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.ChosenCyclicExtension
public import CFSG.Quasithin.Chapter15.Section01.MinimalParabolicSource
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import CFSG.Quasithin.ChapterE.Section02.Structure.WreathRank

/-!
# The cubic residual excludes the symmetric-five wreath local

A cubic action image gives three-rank at most one for the chosen module's
centralizer. The prepared module centralizes O²(H ∩ M), so the same upper
bound holds for H ∩ M. Original15.1.9 identifies this intersection with the
unique maximal subgroup above the Sylow subgroup in H. The symmetric-five
wreath quotient forces that maximal subgroup to have three-rank at least
two, giving the desired contradiction.

Source: Aschbacher--Smith15.1.9(4,7),15.2.3--4, pp.1088--1089,1105--1106.
The exact residual-image calculation remains with the source row producer;
no Omega assumption, normality of Y, or extra Sylow model is used here.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The cubic action-image branch of original15.2.4, retaining the chosen module and H-star local. -/
theorem source_chosen_cubic_HStar_not_symmetricFive_wreath
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 3)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) := by
  rintro ⟨e⟩
  let X := (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype
  have hXC : X ≤ M ⊓ centralizer (V : Set G) :=
    le_inf ((map_subtype_le _).trans inf_le_right) (hV.intersection_residual H hH)
  have hX : primeRank 3 X ≤ 1 :=
    (primeRank_mono 3 hXC).trans
      (source_chosen_cubic_centralizer_rank hG T hM.1 hu hV hcard)
  have he := primeRank_equiv 3 ((pResidual 2 (H ⊓ M : Subgroup G)).equivMapOfInjective
    (H ⊓ M).subtype (H ⊓ M).subtype_injective)
  have hr := ResidualCentralizerRank.primeRank_residual
    (G := (H ⊓ M : Subgroup G)) (by decide : Nat.Coprime 2 3)
  have hintersection : primeRank 3 (H ⊓ M : Subgroup G) ≤ 1 := hr.symm.trans_le (he.trans_le hX)
  obtain ⟨_, hP, hmax, _, _⟩ := source_centralizing_minimalParabolic hG T hM hJ H hH
  have heq := ChapterB.minimalParabolicMax_unique (T.subtype hH.1.1.2) hP hmax
    (show ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) ≤ (H ⊓ M).subgroupOf H from
      fun x hx => ⟨x.property, hM.1.2 hx⟩)
  have hupper : primeRank 3 (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) ≤ 1 := by
    rw [← heq]
    exact (primeRank_equiv 3 (subgroupOfEquivOfLe (show (H ⊓ M : Subgroup G) ≤ H from
      inf_le_left))).trans_le hintersection
  have hlower := ChapterE.Structure.minimalParabolicMax_three_rank_of_symmetricFive_wreath
    (T.subtype hH.1.1.2) hP e
  omega
end CFSG.Quasithin.Chapter15.Section02
