module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Cover
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.TerminalAction

/-!
# G.10 and its SQTK cover on the original nonabelian rank-two closure

Original 14.2.4 constructs the actual rank-two flag and conjugator. Its
point normalizer is the original Mc, and its conjugate span is the original
U. The preceding Frattini, parabolic, center and transvection calculations
then construct G.10.1 for the literal action of H/C_H(U/Z(U)).

The same H is a proper two-local SQTK group, and the defining quotient map
gives its G.9 cover. The actual source result retains the point, Mc, span,
conjugator and quotient action; it has no additional geometry, classification
or irreducibility premise.

Source: Aschbacher--Smith, the setup preceding 14.3.11, 12.8.8--12,
and G.10.1, printed pp.993,851--855.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The rank-two source constructs the literal terminal hypothesis and its SQTK cover. -/
theorem rankTwo_terminal_hypothesis {K : GroupClass} {T : Sylow 2 G} {L M : Subgroup G}
    (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2) [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ClosureGeometry F ∧
    ∃ he : IsElementaryAbelian 2 F.Uhat, letI := he
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat), ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Nonempty (ChapterG.Section09.SQTKCover K F.TerminalHdot) := by
  let d := rankTwo_closure_geometry h F hne
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  let he := F.uhat_elementary_of_point (by decide) d.two d.frattini_point
  let := he
  have a := rankTwo_terminal_earlier h F d hcomm hsquare hne g hgP hgH
  obtain ⟨hx,v,hyp⟩ := terminal_action_hypothesis F d hcomm g
    (F.P_le_G₂ (by decide) L h.L_normalizes_seed hgP) a
  exact ⟨d,he,hx,F.uhatBilinearForm (by decide) d.two d.frattini_point,v,hyp,
    rankTwo_terminal_cover h F⟩

/-- Original 14.3.11 setup for G.10 on the original Mc and conjugate span.
Every earlier geometry premise is discharged by the rank-two source. -/
theorem source_terminal_hypothesis
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ∃ hs : IsElementaryAbelian 2 (rankTwoSeed T M), letI := hs
    ∃ F : InvariantFlag T (rankTwoSeed T M) 2,
      F.Vi 1 = centralInvolutions T ∧ F.H = Mc ∧
      F.U = conjugateSpanBy (localModule T M) Mc ∧ ClosureGeometry F ∧
    ∃ he : IsElementaryAbelian 2 F.Uhat, letI := he
    ∃ g : G, g ∈ F.P (sourceResidual M Mc) ∧ g ∉ F.H ∧
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat), ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let hs := rankTwoSeed_elementary h
  let := hs
  obtain ⟨_,F,_,z,_,_,g,hgP,hgH⟩ := h.exists_flag_geometry
  have hp : F.Vi 1 = centralInvolutions T :=
    (h.sylowOmega_eq_point F).symm.trans (sylowOmega_eq_centralInvolutions T)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hZ,hMc,_⟩ :=
    source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hFH : F.H = Mc := by
    change normalizer (F.Vi 1 : Set G) = Mc
    rw [hp,hMc]
    exact le_antisymm (normalizer_le_centralizer_of_card_two _ hZ) (Subgroup.centralizer_le_normalizer _)
  have hFU : F.U = conjugateSpanBy (localModule T M) Mc := by
    change conjugateSpanBy (rankTwoSeed T M) F.H = _
    rw [hFH,rankTwoSeed_eq_localModule T M]
  have hneF : ¬ IsMulCommutative F.U := hFU ▸ hne
  obtain ⟨d,he,hx,B,v,hyp,hcover⟩ := rankTwo_terminal_hypothesis h F hneF g hgP hgH
  exact ⟨hs,F,hp,hFH,hFU,d,he,g,hgP,hgH,hx,B,v,hyp,hcover⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
