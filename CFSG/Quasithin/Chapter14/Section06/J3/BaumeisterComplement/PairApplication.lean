module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.PointCore
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.ParabolicApplication

/-!
# Baumeister's second parabolic on both original planes

For each original field-affine embedding, identify its actual overlap
normalizer with S₃ × D₁₀ and its literal second/third intersection with
S₃ × C₂. The point centralizer meets O₂(C_G(f)) exactly in ⟨f⟩.
This removes the Lemma 2.5 premise from the original marking
assembly. Only the identification of the generated third parabolic with
A₅ × C₂ remains explicit, as the still-unproved Lemma 2.6 obligation.

Sources: Baumeister (2007), Lemmas 2.5–2.6, p.496;
Aschbacher–Smith, I.4.7(2), 14.3.15.
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
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer


open Janko23.J3Recognition.Ambient.Seventeen
open Sporadic.Janko3.SourceRecognition.Seventeen
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- The original source planes satisfy Lemma 2.5 and the literal pair overlap.
The only retained premise for OriginalMarking is the actual Lemma 2.6 map. -/
theorem source_single_a5_j3_pair_parabolics
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
        ∃ (C : Subgroup (normalizer (A : Set G)))
          (a : A ≃* Representation.CentralCubicNaturalFour.Plane)
          (j : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G),
          Sporadic.Janko3.SourceRecognition.PlaneTransport.FieldEmbedding A C a j ∧
          Nonempty (second (overlap j) ≃* PairGroup) ∧
          Nonempty ((second (overlap j) ⊓ third j.range (overlap j) (j fieldElement) :
            Subgroup G) ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) ∧
          (j.range ⊓ centralizer ({j fieldElement} : Set G)) ⊓
              (pCore 2 (Janko23.involutionCentralizer (j fieldElement))).map
                (Janko23.involutionCentralizer (j fieldElement)).subtype =
            zpowers (j fieldElement) ∧
          (Nonempty (third j.range (overlap j) (j fieldElement) ≃* TriangleGroup) →
            Nonempty (OriginalMarking j.range (overlap j) (j fieldElement))) := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨heA,hcardA,C,_,a,_,_,j,hj⟩ := hfields A hA
  let _ : IsElementaryAbelian 2 A := heA
  have hAR : A ≤ P.R := by
    rcases hA with rfl | rfl
    · exact P.A₁_le_R eR
    · exact P.A₂_le_R eR
  obtain ⟨e2⟩ := Janko23.J3Recognition.Ambient.BaumeisterComplement.field_pair_equiv
    P hc A hcardA hAR j hj.1
  refine ⟨C,a,j,hj,⟨e2⟩,
    ⟨Janko23.J3Recognition.Ambient.BaumeisterParabolics.overlap23Equiv j hj.1 e2⟩,
    Janko23.J3Recognition.Ambient.BaumeisterComplement.field_point_centralizer_core
      (z := D.z) D.localType hc j hj.1,?_⟩
  rintro ⟨e3⟩
  exact ⟨Janko23.J3Recognition.Ambient.BaumeisterParabolics.original_marking_of_pair_triangle
    j hj.1 e2 e3⟩

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
