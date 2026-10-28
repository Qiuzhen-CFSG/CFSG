module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSourceMultiplicityDisplacement
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.SchurHomogeneous

/-!
# The terminal A₆ coordinate consumer of the Schur-rank bound

The original terminal setup supplies homogeneity and faithfulness on the
specified proper constituent. G.10.2 bounds the ambient dimension using the
literal quotient of the original elementary actor. The sole additional input
bounds that actor's binary rank by the constituent's Schur degree plus three.
Schur recognition then constructs actual natural double coordinates on the
original hat module, with a common component marking.

The centralizer-rank producer and the source-theorem assembly retain ownership
of that explicit input. No constituent existence or full A₆×Z₃ extension theorem
is required here. Source: Aschbacher--Smith G.10.2,G.11.7--8 and14.3.15,
printed pp.357,366,368--369,994.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal proper terminal constituent has natural double coordinates
once the elementary actor rank is bounded by its Schur degree plus three. -/
theorem source_terminal_a6_coordinates_of_proper_constituent_schur
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
    (hv : v ∈ I) (hp : I ≠ ⊤)
    (hr :
      let R := BinaryOffender.invariantSubspace F.terminalRepresentation
        (componentOrbit (F.terminalDot K) ⊤) I hI.choose
      Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
        Module.finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) + 3) :
    BinaryAlternatingSixNaturalNormalizer.HasNaturalCoordinates
      (F.terminalRepresentation.comp (F.terminalDot K).subtype) := by
  let L := F.terminalDot K
  let H := componentOrbit L ⊤
  let := hK.alternatingSix_image_normal hG e6
  let := componentOrbit_top_normal L
  have ho : H = L := le_antisymm
    (iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl le_normalizer_of_normal)
    (le_componentOrbit L ⊤)
  have hgeo := Recognition.source_terminal_constituent_homogeneous_of_point_mem
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hK.terminal_not_solvable
    hyp hK.image_component hK.image_moved hI hv
  let R := BinaryOffender.invariantSubspace F.terminalRepresentation H I hI.choose
  let : IsIrreducible R.toRepresentation := hI.irreducible_of_normal_restriction
    F.terminalRepresentation (hyp.irreducible_of_not_solvable hK.terminal_not_solvable) H
  let X := F.terminalDot (F.X g)
  have hq := (Group.rank_le_of_surjective
    (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf X))
    (QuotientGroup.mk'_surjective _)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
  have hd : Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 2 *
      (Module.finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) + 4) := by
    have hb := hyp.dimension_bound.1
    change Module.finrank (ZMod 2) (Additive F.Uhat) ≤
      2 * (Group.rank (X ⧸ (F.terminalDot (conjugate F.ZU g)).subgroupOf X) + 1) at hb
    change Module.finrank (ZMod 2) (Additive X) ≤
      Module.finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) + 3 at hr
    omega
  have hc := ChapterK.Alternating.RecognitionInputs.Six.naturalCoordinates_of_homogeneous_schur_bound
    (F.terminalRepresentation.comp H.subtype) ((MulEquiv.subgroupCongr ho).trans e6) R
    hgeo.2.1 hgeo.1 hp hd
  exact (congrArg (fun A : Subgroup F.TerminalHdot =>
    BinaryAlternatingSixNaturalNormalizer.HasNaturalCoordinates
      (F.terminalRepresentation.comp A.subtype)) ho).mp hc

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
