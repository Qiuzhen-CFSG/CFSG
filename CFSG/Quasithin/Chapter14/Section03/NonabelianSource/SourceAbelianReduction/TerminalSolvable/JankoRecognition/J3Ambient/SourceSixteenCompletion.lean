module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TriangleModelSource
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.Seventeen.Recognition

/-!
# The actual sixteen-field completion in the terminal source

The pair and triangle identifications construct the original Baumeister
marking on the literal embedded field subgroup. Completion recognition then
supplies its PSL₂(16):2 embedding and normal PSL₂(16) subgroup, carrying the
same original involution to the fourth-power field action.

Both original planes retain their normalizer complements and coordinates.
No parabolic model map or completion-recognition premise remains.
Source: Baumeister, A geometry for groups of J₃-type (2007), Corollary 2.10.
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

namespace J3Ambient
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private def literalMarking (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G))) (a : A ≃* Plane)
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    OriginalMarking j.range (overlap j) (j SingerField.fieldElement) :=
  Janko23.J3Recognition.Ambient.BaumeisterParabolics.original_marking_of_pair_triangle
    j hj.1 (literal_overlap_pair_equiv P hc A C a j hj).some
    (literal_triangle_equiv P hc A C a j hj).some

/-- Recognition of the completion on the same original field embedding. -/
theorem literal_sixteen_model_embedding
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G))) (a : A ≃* Plane)
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    ∃ k : Theory.PSL2.BinaryFourFieldExtension.Model →* G,
      Function.Injective k ∧
      k Theory.PSL2.BinaryFourFieldExtension.involution = j SingerField.fieldElement ∧
      k.range = completion j.range (overlap j) :=
  (literalMarking P hc A C a j hj).exists_model_embedding

/-- The actual completion contains its normal linear factor with the original
field involution acting by fourth-power Frobenius. -/
theorem literal_sixteen_linear_subgroup
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G))) (a : A ≃* Plane)
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    ∃ (J : Subgroup G) (eJ : J ≃* Theory.PSL2.BinaryGroup 4),
      J ≤ completion j.range (overlap j) ∧
      (J.subgroupOf (completion j.range (overlap j))).Normal ∧
      Nat.card J = 4080 ∧ j SingerField.fieldElement ∉ J ∧
      orderOf (j SingerField.fieldElement) = 2 ∧
      j SingerField.fieldElement ∈ normalizer (J : Set G) ∧
      J ⊔ zpowers (j SingerField.fieldElement) = completion j.range (overlap j) ∧
      ∀ x : Theory.PSL2.BinaryGroup 4,
        j SingerField.fieldElement * (eJ.symm x : G) * (j SingerField.fieldElement)⁻¹ =
          (eJ.symm (Theory.PSL2.fieldAut
            Theory.PSL2.BinaryFourFieldExtension.fieldInvolution x) : G) :=
  (literalMarking P hc A C a j hj).exists_linear_subgroup

end J3Ambient

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

/-- Both original terminal planes produce the actual marked sixteen-field
completion and its linear subgroup, retaining their full source coordinates. -/
theorem source_single_a5_j3_sixteen_completion_of_four
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
            (∃ k : Theory.PSL2.BinaryFourFieldExtension.Model →* G,
              Function.Injective k ∧
              k Theory.PSL2.BinaryFourFieldExtension.involution = j SingerField.fieldElement ∧
              k.range = completion j.range (overlap j)) ∧
            ∃ (J : Subgroup G) (eJ : J ≃* Theory.PSL2.BinaryGroup 4),
              J ≤ completion j.range (overlap j) ∧
              (J.subgroupOf (completion j.range (overlap j))).Normal ∧
              Nat.card J = 4080 ∧ j SingerField.fieldElement ∉ J ∧
              orderOf (j SingerField.fieldElement) = 2 ∧
              j SingerField.fieldElement ∈ normalizer (J : Set G) ∧
              J ⊔ zpowers (j SingerField.fieldElement) = completion j.range (overlap j) ∧
              ∀ x : Theory.PSL2.BinaryGroup 4,
                j SingerField.fieldElement * (eJ.symm x : G) * (j SingerField.fieldElement)⁻¹ =
                  (eJ.symm (Theory.PSL2.fieldAut
                    Theory.PSL2.BinaryFourFieldExtension.fieldInvolution x) : G) := by
  obtain ⟨hc, D, P, eR, hHK, hHz, hcore, hneP, hsup, hinf, hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc, D, P, eR, hHK, hHz, hcore, hneP, hsup, hinf, ?_⟩
  intro A hA
  obtain ⟨hAE, hAc, C, f, a, hC, ha, j, hj⟩ := hfields A hA
  exact ⟨hAE, hAc, C, f, a, hC, ha, j, hj,
    J3Ambient.literal_sixteen_model_embedding P hc A C a j hj,
    J3Ambient.literal_sixteen_linear_subgroup P hc A C a j hj⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
