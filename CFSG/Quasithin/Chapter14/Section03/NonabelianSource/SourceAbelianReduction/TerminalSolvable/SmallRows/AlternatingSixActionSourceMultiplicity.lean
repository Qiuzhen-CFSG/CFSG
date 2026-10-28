module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSourceIrreducible
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.Homogeneous
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Homogeneous

/-!
# Natural coordinates from the proper terminal constituent and a degree bound

The full binary A₆ catalogue and constituent faithfulness force a simple
constituent of degree at most eight to have degree four. Homogeneity and
properness then give two copies on the original module. Four-space recognition
marks the constituent, and the same marking on both copies gives actual
intertwining coordinates on the original hat module.

The degree bound is an explicit source obligation here. In particular this
module does not infer faithfulness of the elementary actor from faithfulness
of the component on its constituent.

Source: Aschbacher--Smith G.11.7 and G.11.2(10), printed pp.364,366,
and the A₆ paragraph of 14.3.15, printed p.994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06


variable {G : Type*} [Group G] [Finite G]

/-- Discharge the coordinate callback on the original terminal module once
the original degree is bounded. No multiplicity or action marking is assumed. -/
theorem source_terminal_a6_coordinates_of_proper_constituent_degree
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
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 8) :
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
  have hc := ChapterK.Alternating.RecognitionInputs.Six.naturalCoordinates_of_homogeneous_degree_le_eight
    (F.terminalRepresentation.comp H.subtype) ((MulEquiv.subgroupCongr ho).trans e6) R
    hgeo.2.1 hgeo.1 hp hd
  exact (congrArg (fun A : Subgroup F.TerminalHdot =>
    BinaryAlternatingSixNaturalNormalizer.HasNaturalCoordinates
      (F.terminalRepresentation.comp A.subtype)) ho).mp hc

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G]

/-- A trivial centralizer intersection bounds the original elementary actor,
without assuming an irreducible action on the whole hat module. -/
theorem ComponentLift.alternatingSix_degree_le_eight_of_actor_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2}
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    {g : G} {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hc : F.terminalDot (F.X g) ⊓ centralizer (F.terminalDot K : Set F.TerminalHdot) = ⊥) :
    Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 8 := by
  let L := F.terminalDot K
  let X := F.terminalDot (F.X g)
  let := hK.alternatingSix_image_normal hG e6
  have hn : X ≤ normalizer (L : Set F.TerminalHdot) := le_normalizer_of_normal
  let f := L.normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hxC : (x : F.TerminalHdot) ∈ centralizer (L : Set F.TerminalHdot) := by
      change Subgroup.inclusion hn x ∈ L.normalizerMonoidHom.ker at hx
      rw [Subgroup.normalizerMonoidHom_ker] at hx
      exact hx
    have hxbot : (x : F.TerminalHdot) ∈ (⊥ : Subgroup F.TerminalHdot) := hc ▸ ⟨x.property,hxC⟩
    exact hxbot
  let : CommGroup X := IsMulCommutative.instCommGroup
  have hr : Module.finrank (ZMod 2) (Additive X) ≤ primeRank 2 (MulAut L) := by
    apply primeRank_ge_of_elementary_embedding
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 X)) ?_ f hf
    change Nat.card (Additive X) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [primeRank_equiv 2 (MulAut.congr e6)] at hr
  have ha := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.alternating_six_automorphism_two_rank
  have hq := (Group.rank_le_of_surjective
    (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf X))
    (QuotientGroup.mk'_surjective _)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
  have hd := hyp.dimension_bound.1
  change Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 2 *
    (Group.rank (X ⧸ (F.terminalDot (conjugate F.ZU g)).subgroupOf X) + 1) at hd
  omega
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The faithful-conjugation branch is discharged. Only the dimension bound
for a nontrivial actor centralizer remains as an earlier source input. -/
theorem source_terminal_a6_coordinates_of_nonfaithful_degree_bound
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
    (hbound : F.terminalDot (F.X g) ⊓
      centralizer (F.terminalDot K : Set F.TerminalHdot) ≠ ⊥ →
      Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 8) :
    BinaryAlternatingSixNaturalNormalizer.HasNaturalCoordinates
      (F.terminalRepresentation.comp (F.terminalDot K).subtype) := by
  have hd : Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 8 := by
    by_cases hc : F.terminalDot (F.X g) ⊓
        centralizer (F.terminalDot K : Set F.TerminalHdot) = ⊥
    · exact hK.alternatingSix_degree_le_eight_of_actor_centralizer hG e6 hyp hc
    · exact hbound hc
  exact source_terminal_a6_coordinates_of_proper_constituent_degree
    hG T hempty hM hu hmany hcard e F _hnot hne g hgP hgH hK e6 hyp hI hv hp hd

/-- Apply the proper-constituent coordinates to the literal radical-quotient
Sylow action used by the small-row exclusion. -/
theorem source_terminal_a6_natural_action_of_proper_constituent_degree
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
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 8) :
    hK.AlternatingSixNaturalAction e6 := by
  exact hK.alternatingSixNaturalAction_of_coordinates hG e6
    (source_terminal_a6_coordinates_of_proper_constituent_degree
      hG T hempty hM hu hmany hcard e F _hnot hne g hgP hgH hK e6 hyp hI hv hp hd)


/-- The original natural-action assembly now needs only proper-constituent
existence and the nonfaithful degree bound. The irreducible branch and the
proper branch's coordinate construction are proved. -/
theorem source_terminal_a6_natural_action_of_point_and_nonfaithful_degree
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
    (hpoint : ¬ IsIrreducible (F.terminalRepresentation.comp (F.terminalDot K).subtype) →
      ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
        BinaryOffender.IsIrrPlus F.terminalRepresentation
          (componentOrbit (F.terminalDot K) ⊤) I ∧ v ∈ I ∧ I ≠ ⊤)
    (hbound : ∀ I : Submodule (ZMod 2) (Additive F.Uhat),
      BinaryOffender.IsIrrPlus F.terminalRepresentation
        (componentOrbit (F.terminalDot K) ⊤) I → v ∈ I → I ≠ ⊤ →
      F.terminalDot (F.X g) ⊓ centralizer (F.terminalDot K : Set F.TerminalHdot) ≠ ⊥ →
      Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 8) :
    hK.AlternatingSixNaturalAction e6 := by
  apply source_terminal_a6_natural_action_of_constituent_inputs
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hK e6 hyp hpoint
  intro I hI hv hp
  exact source_terminal_a6_coordinates_of_nonfaithful_degree_bound
    hG T hempty hM hu hmany hcard e F _hnot hne g hgP hgH hK e6 hyp hI hv hp
    (hbound I hI hv hp)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
