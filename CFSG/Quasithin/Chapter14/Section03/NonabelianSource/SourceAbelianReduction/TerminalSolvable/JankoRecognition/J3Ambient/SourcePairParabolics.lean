module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.OverlapPair
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.BaumeisterParabolics

/-!
# The literal pair parabolic and both overlaps in the terminal J₃ source

For each original terminal plane, retain its actual normalizer complement,
linear coordinates and field embedding. The normalizer of the same embedded
C₃ × D₁₀ is now S₃ × D₁₀. Both intersections with the same third parabolic
therefore have their concrete A₄ × C₂ and S₃ × C₂ models, without a pair
recognition premise or a change of field embedding.

The third parabolic itself still requires its separate A₅ × C₂ identification.
Source: Baumeister, A geometry for groups of J₃-type (2007), Lemmas 2.5–2.6.
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

/-- Both original field embeddings supply the actual pair model and both
literal parabolic overlaps, preserving their normalizer complements. -/
theorem source_single_a5_j3_pair_parabolics_of_four
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
        IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
        ∃ (C : Subgroup (normalizer (A : Set G))) (f : C ≃* LinearGroup) (a : A ≃* Plane),
          (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
          (∀ (c : C) (x : A),
            a (A.normalizerMonoidHom c x) = naturalAction (f c) (a x)) ∧
          ∃ j : SingerField.Model →* G,
            PlaneTransport.FieldEmbedding A C a j ∧
            Nonempty (second (overlap j) ≃* Sporadic.Janko3.SourceRecognition.Seventeen.PairGroup) ∧
            Nonempty ((j.range ⊓ third j.range (overlap j) (j SingerField.fieldElement) : Subgroup G) ≃*
              (alternatingGroup (Fin 4) × Multiplicative (ZMod 2))) ∧
            Nonempty ((second (overlap j) ⊓ third j.range (overlap j) (j SingerField.fieldElement) :
              Subgroup G) ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) := by
  obtain ⟨hc, D, P, eR, hHK, hHz, hcore, hneP, hsup, hinf, hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc, D, P, eR, hHK, hHz, hcore, hneP, hsup, hinf, ?_⟩
  intro A hA
  obtain ⟨hAE, hAc, C, f, a, hC, ha, j, hj⟩ := hfields A hA
  obtain ⟨hp⟩ := J3Ambient.literal_overlap_pair_equiv P hc A C a j hj
  exact ⟨hAE, hAc, C, f, a, hC, ha, j, hj, ⟨hp⟩,
    ⟨Janko23.J3Recognition.Ambient.BaumeisterParabolics.overlap13Equiv j hj.1⟩,
    ⟨Janko23.J3Recognition.Ambient.BaumeisterParabolics.overlap23Equiv j hj.1 hp⟩⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
