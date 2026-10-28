module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSourceMultiplicity
public import CFSG.Quasithin.ChapterG.Section10.Components.CentralizerDisplacement

/-!
# Displacements of centralizing actors on the original terminal A₆ module

The original marked-constituent geometry and component normality put every
centralizing actor's displacement in the same constituent. Faithfulness and
simplicity give equality for each nonidentity actor, and the original
alternating form identifies its kernel with the constituent's orthogonal.
This supplies the literal module maps for the remaining Schur-field rank
bound; it does not assume that bound or the final natural coordinates.

Source: Aschbacher--Smith G.10.12 and the multiplicity argument following
G.11.7, printed pp.360,368--369, applied to14.3.15, printed p.994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- On the literal original hat module, every nonidentity element of
X centralizing the marked A₆ component has image I and kernel I-perpendicular. -/
theorem source_terminal_a6_centralizer_displacement
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
    (hv : v ∈ I) (_hp : I ≠ ⊤)
    (c : F.terminalDot (F.X g))
    (hc : (c : F.TerminalHdot) ∈ centralizer (F.terminalDot K : Set F.TerminalHdot))
    (hc1 : c ≠ 1) :
    LinearMap.range (F.terminalRepresentation c - LinearMap.id) = I ∧
      LinearMap.ker (F.terminalRepresentation c - LinearMap.id) = B.orthogonal I := by
  let L := F.terminalDot K
  let H := componentOrbit L ⊤
  let := hK.alternatingSix_image_normal hG e6
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hK.image_component.orbit_isPerfect ⊤
  have ho : H = L := le_antisymm
    (iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl le_normalizer_of_normal)
    (le_componentOrbit L ⊤)
  have hgeo := Recognition.source_terminal_constituent_homogeneous_of_point_mem
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hK.terminal_not_solvable
    hyp hK.image_component hK.image_moved hI hv
  let R := BinaryOffender.invariantSubspace F.terminalRepresentation H I hI.choose
  have hi := hyp.irreducible_of_not_solvable hK.terminal_not_solvable
  have hR : IsIrreducible R.toRepresentation := hI.irreducible_of_normal_restriction
    F.terminalRepresentation hi H
  apply hyp.centralizer_displacement_range_and_ker hi H
    hK.image_component.componentOrbit_top_ne_bot R hR hgeo.1 hv
    (hI.finrank_gt_two F.terminalRepresentation H) c
  · rw [ho]
    exact hc
  · exact hc1

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
