module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CubicRecognition
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3PlaneNatural

/-!
# Cubic centralizer quotients in the original terminal J₃ row

The complete original selected-row hypotheses supply the H-type seed,
returning pair and marked elementary planes. For each original plane,
choose a central cubic in an actual normalizer complement. Its full ambient
centralizer modulo that same cubic is now identified with A₆. Every source
premise is supplied by the original terminal prefix; no recognition, order
or quotient-isomorphism assumption is added.

This is the centralizer-quotient step of Baumeister Lemma 2.4 applied to
Aschbacher–Smith 14.3.15 and I.4.7(2). The normalizer, splitting, rank-three
amalgam, presentation/kernel comparison and terminal-solvability conclusion
remain separate obligations. The original component and core identifications,
and both actual planes, remain marked in the conclusion.

Sources: Baumeister (2007), p.495; Aschbacher–Smith, pp.418,994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
section Source
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

variable (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hnot hgP hgH hyp hK


include hG hempty hM hu hmany hcard e hne

open Janko23.J3Recognition.LocalSixteen

open Representation.CentralCubicNaturalFour

open Janko23.J3Recognition.Ambient

/-- Baumeister's centralizer-quotient step, applied without extra hypotheses to the original terminal row. -/
theorem source_single_a5_j3_cubic_quotients_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Janko23.OneInvolutionClass G ∧
    ∃ (D : Seed G) (P : ReturningPair D)
      (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root),
      F.H = K ∧ F.H = Janko23.involutionCentralizer D.z ∧
      Janko23.ambientCore D.z = F.U ∧
      P.A₁ eR ≠ P.A₂ eR ∧ P.A₁ eR ⊔ P.A₂ eR = P.R ∧ P.A₁ eR ⊓ P.A₂ eR = P.E ∧
      ∀ A : Subgroup G, A = P.A₁ eR ∨ A = P.A₂ eR →
        ∃ (C : Subgroup (normalizer (A : Set G))) (s : C),
          (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
          Nat.card C = 180 ∧ s ∈ center C ∧ orderOf s = 3 ∧
          Nonempty ((centralizer ({((s : normalizer (A : Set G)) : G)} : Set G) ⧸
            cubicKernel ((s : normalizer (A : Set G)) : G)) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hc,D,P,eR,_,_,hHK,hHz,hcore,_⟩ :=
    source_single_a5_j3_local_sixteen_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,P.planes_ne eR,P.planes_sup eR,P.planes_inf eR,?_⟩
  intro A hA
  have hAR : A ≤ P.R := by
    rcases hA with rfl | rfl
    · exact P.A₁_le_R eR
    · exact P.A₂_le_R eR
  have he := (P.elementary_sixteen_iff eR A hAR).mpr hA
  let : IsElementaryAbelian 2 A := he.1
  exact plane_cubic_quotient_alternatingSix P hc A he.2 hAR

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
