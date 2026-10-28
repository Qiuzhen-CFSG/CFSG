module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.SourceMarkedAmalgam
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.ThreePairModelSource
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CompletionCubicGeneration
public import Theory.SpecificGroups.Janko3.SourceRecognition.PlaneFieldCompatibility

/-!
# All three compatible local models under the original terminal source prefix

Both original planes retain their original natural complement, field map,
faithful affine extension, sixteen-field completion, and actual order-243
subgroup. The constructed local equivalences agree pointwise on all three
full intersections, and the literal completion and cubic normalizer generate
the original ambient group. No matching maps or presentation relations are
assumed. The cubic complement returned here is the one selected by the
three-model construction; it is not identified with another chosen complement.
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

/-- The original terminal hypotheses construct all three local models with
full pointwise overlap agreement, both original planes, and cubic growth. -/
theorem source_single_a5_j3_three_pair_models_of_four
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
          ∃ (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j),
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
            (∃ E Q : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 27 ∧ j cubic ∈ E ∧
              Nat.card {x : E // IsConj (j cubic) (x : G)} = 18 ∧
              E ≤ Q ∧ Q ≤ normalizer (E : Set G) ∧ Nat.card Q = 243) ∧
            completion j.range (overlap j) ⊔ normalizer (zpowers (j cubic) : Set G) = ⊤ ∧
            let L := completion j.range (overlap j)
            let N := normalizer (zpowers (j cubic) : Set G)
            ∃ (K : Subgroup N) (e₁ : L ≃* Theory.PSL2.BinaryFourFieldExtension.Model)
              (e₃ : N ≃* CubicNormalizerModel.Model)
              (e₂ : normalizer (A : Set G) ≃* Plane ⋊[naturalAction] LinearGroup),
              (cubicNormalizerKernel (j cubic)).IsComplement' K ∧
              ((L ⊓ N).subgroupOf L).map e₁.toMonoidHom =
                Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair ∧
              ((L ⊓ N).subgroupOf N).map e₃.toMonoidHom = CubicNormalizerModel.pair ∧
              (cubicNormalizerKernel (j cubic)).map e₃.toMonoidHom =
                CubicNormalizerModel.projection.ker ∧
              K.map e₃.toMonoidHom =
                (SemidirectProduct.inr : CubicNormalizerModel.P →* CubicNormalizerModel.Model).range ∧
              ((normalizer (A : Set G)).subgroupOf N).map e₃.toMonoidHom =
                CubicNormalizerModel.thirdOverlap ∧
              ((j.range).subgroupOf L).map e₁.toMonoidHom =
                Seventeen.ModelAmalgam.point ∧
              C.map e₂.toMonoidHom =
                (SemidirectProduct.inr : LinearGroup →* Plane ⋊[naturalAction] LinearGroup).range ∧
              (∀ x : j.range, ∃ z : Seventeen.ModelAmalgam.point,
                e₁ ⟨x,(show j.range ≤ L from le_sup_left) x.property⟩ = (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∧
                e₂ ⟨x,hj.2.1 x.property⟩ =
                  SingerField.affineEmbedding (Seventeen.ModelAmalgam.SingerPoint.pointEquiv.symm z)) ∧
              (∀ x : (normalizer (A : Set G) ⊓ N : Subgroup G), ∃ z : LinearGroup,
                e₂ ⟨x,x.property.1⟩ = SemidirectProduct.inr z ∧
                e₃ ⟨x,x.property.2⟩ =
                  (CubicNormalizerModel.linearThirdEquiv z : CubicNormalizerModel.Model)) ∧
              ∀ x : (L ⊓ N : Subgroup G),
                ∃ z : Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair,
                  e₁ ⟨x,x.property.1⟩ = (z : Theory.PSL2.BinaryFourFieldExtension.Model) ∧
                  e₃ ⟨x,x.property.2⟩ =
                    (CubicNormalizerModel.modelPairEquiv z : CubicNormalizerModel.Model) := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hfields⟩ :=
    source_single_a5_j3_marked_amalgam_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨hAE,hAc,C,l,a,hC,ha,j,hj,hmodel,hgrowth,_⟩ := hfields A hA
  exact ⟨hAE,hAc,C,l,a,hC,ha,j,hj,
    PlaneTransport.affine_embedding_extending_fieldEmbedding A C l a hC ha j hj,
    hmodel,hgrowth,
    J3Ambient.literal_completion_cubic_normalizer_generate P hc A C a j hj,
    J3Ambient.literal_canonical_three_pair_models P hc A C l a hC ha j hj⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
