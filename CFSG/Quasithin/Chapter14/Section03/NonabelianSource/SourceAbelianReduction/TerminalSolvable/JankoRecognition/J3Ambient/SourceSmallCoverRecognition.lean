module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.SourceCubicGrowth
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.SmallCover

/-!
# The original terminal source recognized from a genuine small cover

All local inputs of bounded-cover recognition are now constructed under the
original terminal hypotheses: the H-type involution, unique involution class,
order-243 subgroup and injective sixteen-field completion. Only the genuinely
finite cover with its order bound and its two surjections remains to be supplied.
No source ATLAS generators, local model maps or independent lower bound are inputs.
-/

public noncomputable section
open Subgroup
open Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hG hempty hM hu hmany hcard e hne hnot hgP hgH hyp hK

/-- The original terminal row is the concrete J₃ model as soon as its actual
bounded cover and the two generating projections have been certified. -/
theorem source_single_a5_j3_equiv_of_small_cover_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    {E : Type*} [Group E] [Finite E]
    (f : E →* Sporadic.Janko3.Model) (hf : Function.Surjective f)
    (q : E →* G) (hq : Function.Surjective q) (hbound : Nat.card E ≤ 150698880) :
    ∃ e : Sporadic.Janko3.Model ≃* G, e.toMonoidHom.comp f = q := by
  obtain ⟨hc,D,P,eR,_hHK,_hHz,_hcore,_hneP,_hsup,_hinf,hfields⟩ :=
    source_single_a5_j3_cubic_growth_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_hAE,_hAc,C,l,a,_hC,_ha,j,_hj,⟨k,hk,_⟩,_hgen,_hsplit,
      _E,Q,_hE,_hcE,_hsE,_horbit,_hEQ,_hQN,hQ⟩ := hfields (P.A₁ eR) (Or.inl rfl)
  let : IsSimpleGroup G := hG.simple
  have hcenter : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) inferInstance with h | h
    · exact h
    · exact (hG.nonabelian (center_eq_top_iff.mp h)).elim
  exact Janko23.J3Recognition.equiv_of_small_cover_and_local_subgroups
    ⟨⟨D.z,D.localType⟩,hc⟩ hcenter Q hQ k hk f hf q hq hbound

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
