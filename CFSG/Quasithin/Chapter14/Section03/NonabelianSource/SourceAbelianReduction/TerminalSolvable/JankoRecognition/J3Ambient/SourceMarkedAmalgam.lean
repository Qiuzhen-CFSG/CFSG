module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.SourceCubicGrowth
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.MarkedAmalgamSource

/-!
# Original terminal source for the marked generating J₃ amalgam

Both original planes retain the same complements, natural actions and field
embeddings. Each gives the actual L₂(16):2 completion, an actual order-243
subgroup, and a PGL₂(9) complement generating the whole group with that
completion. The complement retains its literal A₅ plane intersection and
D₂₀ pair intersection, including the original dihedral factor and inverter.
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

/-- The complete marked generating local source under the original terminal
hypotheses, with both original planes and no recognition or placement input. -/
theorem source_single_a5_j3_marked_amalgam_of_four
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
            (∃ k : Theory.PSL2.BinaryFourFieldExtension.Model →* G,
              Function.Injective k ∧
              k Theory.PSL2.BinaryFourFieldExtension.involution = j SingerField.fieldElement ∧
              k.range = completion j.range (overlap j)) ∧
            (∃ E Q : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 27 ∧ j cubic ∈ E ∧
              Nat.card {x : E // IsConj (j cubic) (x : G)} = 18 ∧
              E ≤ Q ∧ Q ≤ normalizer (E : Set G) ∧ Nat.card Q = 243) ∧
            let s := j cubic
            let f := j SingerField.fieldElement
            let N := normalizer (zpowers s : Set G)
            let D₀ := (_root_.commutator (centralizer ({s} : Set G))).map
              (inclusion (cubic_centralizer_le_normalizer s))
            ∃ (B : Subgroup G) (y : N) (K : Subgroup N),
              (∀ x, x ∈ B ↔ x ∈ overlap j ∧ x ^ 10 = 1) ∧
              Nonempty (B ≃* DihedralGroup 5) ∧ f ∈ B ∧
              (y : G) ∈ normalizer (overlap j : Set G) ∧ orderOf y = 2 ∧
              (y : G) * s * (y : G)⁻¹ = s⁻¹ ∧
              (∀ b ∈ B, Commute (y : G) b) ∧
              K = D₀ ⊔ zpowers y ∧
              (cubicNormalizerKernel s).IsComplement' K ∧
              Nonempty (K ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) ∧
              B ≤ K.map N.subtype ∧
              normalizer (overlap j : Set G) ⊓ K.map N.subtype = B ⊔ zpowers (y : G) ∧
              Nonempty ((normalizer (overlap j : Set G) ⊓ K.map N.subtype : Subgroup G) ≃*
                (Multiplicative (ZMod 2) × DihedralGroup 5)) ∧
              normalizer (A : Set G) ⊓ K.map N.subtype =
                (_root_.commutator C).map ((normalizer (A : Set G)).subtype.comp C.subtype) ∧
              Nonempty ((normalizer (A : Set G) ⊓ K.map N.subtype : Subgroup G) ≃*
                alternatingGroup (Fin 5)) ∧
              completion j.range (overlap j) ⊔ K.map N.subtype = ⊤
 := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hfields⟩ :=
    source_single_a5_j3_cubic_growth_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨hAE,hAc,C,l,a,hC,ha,j,hj,hmodel,_hgen,_hsplit,hgrowth⟩ := hfields A hA
  exact ⟨hAE,hAc,C,l,a,hC,ha,j,hj,hmodel,hgrowth,
    J3Ambient.literal_marked_amalgam_source P hc A C l a hC ha j hj⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
