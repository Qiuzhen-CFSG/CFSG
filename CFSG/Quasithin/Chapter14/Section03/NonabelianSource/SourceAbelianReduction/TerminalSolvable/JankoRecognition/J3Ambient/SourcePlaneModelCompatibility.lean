module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.SourceRankThreeGeneration
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneFieldCompatibility

/-!
# The affine model on the same original J₃ field subgroup

Both original terminal planes carry faithful affine-model embeddings onto their
whole normalizers. Each model map restricts pointwise to the same field-affine
embedding used by the actual sixteen-field completion and cubic normalizer.
The original whole-group generation and full cubic complement are retained.
This supplies the plane side of the marked rank-three amalgam comparison; no
universal-completion bound or presentation recognition is assumed.
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

/-- The original generating rank-three source retains an affine model map
that agrees pointwise on its entire original field-affine overlap. -/
theorem source_single_a5_j3_plane_model_compatibility_of_four
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
        ∃ (C : Subgroup (normalizer (A : Set G))) (l : C ≃* LinearGroup) (a : A ≃* Plane),
          (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
          (∀ (c : C) (x : A),
            a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x)) ∧
          ∃ j : SingerField.Model →* G,
            PlaneTransport.FieldEmbedding A C a j ∧
            (∃ k : Plane ⋊[naturalAction] LinearGroup →* G,
              Function.Injective k ∧ k.range = normalizer (A : Set G) ∧
              k.comp SingerField.affineEmbedding = j ∧
              (∀ x : Plane, k (SemidirectProduct.inl x) = (a.symm x : G)) ∧
              ∀ c : C, k (SemidirectProduct.inr (l c)) =
                ((c : normalizer (A : Set G)) : G)) ∧
            (∃ k : Theory.PSL2.BinaryFourFieldExtension.Model →* G,
              Function.Injective k ∧
              k Theory.PSL2.BinaryFourFieldExtension.involution = j SingerField.fieldElement ∧
              k.range = completion j.range (overlap j)) ∧
            completion j.range (overlap j) ⊔ normalizer (zpowers (j cubic) : Set G) = ⊤ ∧
            ∃ K : Subgroup (normalizer (zpowers (j cubic) : Set G)),
              (Janko23.J3Recognition.Ambient.cubicNormalizerKernel (j cubic)).IsComplement' K ∧
              Nonempty (K ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hfields⟩ :=
    source_single_a5_j3_rank_three_generation_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨hAE,hAc,C,l,a,hC,ha,j,hj,hmodel,hgenerate,hcubic⟩ := hfields A hA
  exact ⟨hAE,hAc,C,l,a,hC,ha,j,hj,
    PlaneTransport.affine_embedding_extending_fieldEmbedding A C l a hC ha j hj,
    hmodel,hgenerate,hcubic⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
