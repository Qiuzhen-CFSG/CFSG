module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Source
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Normality
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Construction

/-!
# The original terminal actor is normal in the dotted Sylow subgroup

The original parabolic generation gives the containment of X in T. The
point commutator and point-plane factorization make its literal terminal
image normal in the image of T. Surjectivity of the defining quotient map
makes that image a Sylow subgroup without an assumption on the action kernel.
This supplies the source G.11.1(4) mark used to exclude the nonsolvable
faithful-Fitting branch of G.11.5.
Source: Aschbacher--Smith, 12.8.12(2), G.11.1(4), and 14.3.15.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem rankTwo_terminal_actor_normal_in_sylow
    {K : GroupClass} {T : Sylow 2 G} {L M : Subgroup G}
    (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g∈F.P L) (hgH : g∉F.H) :
    let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
      (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    F.terminalDot (F.X g)≤(P:Subgroup F.TerminalHdot) ∧
      ((F.terminalDot (F.X g)).subgroupOf (P:Subgroup F.TerminalHdot)).Normal := by
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  have hnat : 3≤2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hspan : F.U=conjugateSpanBy (F.Vi 2) F.H := by rw [F.last];rfl
  obtain ⟨e,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed
      (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare hspan hne g hgP hgH
  have hcore' := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex
  obtain ⟨z,hz,hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  exact Xdot_normal_in_Tdot F (by decide) z hzp hz
    (F.binary_point_commutator (by decide) hcomm hindex) L g
    (F.P_le_G₂ (by decide) L h.L_normalizes_seed hgP) hIG
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN) hcore'
    F.terminalHatAction F.terminalHatAction_apply_mk

theorem source_terminal_actor_normal_in_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T=∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G))={Mc})
    (hmany : 1<(maximalTwoLocalOvergroups (T:Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M)=4)
    (e : (M⧸(centralizer (localModule T M:Set G)).subgroupOf M)≃*Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H) :
    let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
      (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    F.terminalDot (F.X g)≤(P:Subgroup F.TerminalHdot) ∧
      ((F.terminalDot (F.X g)).subgroupOf (P:Subgroup F.TerminalHdot)).Normal := by
  exact rankTwo_terminal_actor_normal_in_sylow
    (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e) F hne g hgP hgH
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
