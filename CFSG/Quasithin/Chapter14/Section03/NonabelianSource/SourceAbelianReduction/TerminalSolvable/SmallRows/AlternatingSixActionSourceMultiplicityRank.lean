module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSourceMultiplicitySchur
public import Theory.Representation.BinaryOffender.Homogeneous.SchurDisplacementRank
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover

/-!
# Schur rank and coordinates on the original terminal A₆ module

The original marked-constituent displacement theorem supplies common image I
and common kernel I-perpendicular for the centralizing elementary actor.
The quotient construction embeds that centralizer in End_L(I). The literal
conjugation kernel and the proved two-rank bound for Aut(A₆) then give
rank(X) ≤ dim End_L(I) + 3. Component normality identifies its orbit with L.

The second theorem discharges the sole rank premise of the existing Schur
coordinate endpoint, yielding actual natural double coordinates on the original
hat module. All original finite simple-QTKE and marked proper-constituent
hypotheses are retained; no actor-faithfulness or multiplicity bound is added.

Source: Aschbacher--Smith G.10.12 and the homogeneous argument following
G.11.7, printed pp.360,368--369, applied to14.3.15, printed pp.993--994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original elementary actor has binary rank at most the constituent's
Schur degree plus three, with no additional rank or faithfulness premise. -/
theorem source_terminal_a6_actor_finrank_le_schur_add_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (_hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : BinaryOffender.IsIrrPlus F.terminalRepresentation
      (componentOrbit (F.terminalDot K) ⊤) I)
    (hv : v ∈ I) (hp : I ≠ ⊤) :
    let R := BinaryOffender.invariantSubspace F.terminalRepresentation
      (componentOrbit (F.terminalDot K) ⊤) I hI.choose
    Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) + 3 := by
  let L := F.terminalDot K
  let H := componentOrbit L ⊤
  let := hK.alternatingSix_image_normal hG e6
  let := componentOrbit_top_normal L
  have ho : H = L := le_antisymm
    (iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl le_normalizer_of_normal)
    (le_componentOrbit L ⊤)
  let R := BinaryOffender.invariantSubspace F.terminalRepresentation H I hI.choose
  have hd (c : F.terminalDot (F.X g))
      (hc : (c : F.TerminalHdot) ∈ centralizer (H : Set F.TerminalHdot))
      (hc1 : c ≠ 1) :
      LinearMap.range (F.terminalRepresentation c - LinearMap.id) = R.toSubmodule ∧
      LinearMap.ker (F.terminalRepresentation c - LinearMap.id) = B.orthogonal I := by
    apply source_terminal_a6_centralizer_displacement hG T hempty hM hu hmany hcard e
      F _hnot hne g hgP hgH hK e6 hyp hI hv hp c
    · rwa [ho] at hc
    · exact hc1
  have hb := BinaryOffender.finrank_le_schur_add_automorphism_rank
    F.terminalRepresentation hyp.faithful H (F.terminalDot (F.X g)) R (B.orthogonal I) hd
  have ha : primeRank 2 (MulAut H) ≤ 3 := by
    rw [primeRank_equiv 2 (MulAut.congr ((MulEquiv.subgroupCongr ho).trans e6))]
    exact ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.alternating_six_automorphism_two_rank
  exact hb.trans (Nat.add_le_add_left ha _)

/-- Discharge the Schur-rank input and obtain actual natural coordinates from
the original proper marked terminal constituent. -/
theorem source_terminal_a6_coordinates_of_proper_constituent
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (_hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : BinaryOffender.IsIrrPlus F.terminalRepresentation
      (componentOrbit (F.terminalDot K) ⊤) I)
    (hv : v ∈ I) (hp : I ≠ ⊤) :
    BinaryAlternatingSixNaturalNormalizer.HasNaturalCoordinates
      (F.terminalRepresentation.comp (F.terminalDot K).subtype) := by
  exact source_terminal_a6_coordinates_of_proper_constituent_schur
    hG T hempty hM hu hmany hcard e F _hnot hne g hgP hgH hK e6 hyp hI hv hp
    (source_terminal_a6_actor_finrank_le_schur_add_three
      hG T hempty hM hu hmany hcard e F _hnot hne g hgP hgH hK e6 hyp hI hv hp)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
