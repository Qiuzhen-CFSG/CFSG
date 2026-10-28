module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.BaumeisterParabolics
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.Seventeen

/-!
# Baumeister's point-side marking in the original terminal row

Apply the field-affine construction to both original planes. For each actual
embedded L₁, construct its C₃ × D₁₀ complement, the cubic and involution, and
prove the first normalizer intersection and self-centralizing two-core.
The first/third overlap is identified with A₄ × C₂ on these same subgroups.
The second/third overlap is identified with S₃ × C₂ once Lemma 2.5
identifies the actual second parabolic. No centralizer marking is assumed.
These conclusions supply the literal overlap data for the existing
seventeen-point consumer.

The second/third group identifications, and hence construction of the full
`OriginalMarking`, remain to be proved. The full KnownSimple/proper-K source
hypotheses are retained.

Sources: Baumeister (2007), pp.495–496; Aschbacher–Smith I.4.7(2), 14.3.15.
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

/-- The original terminal planes supply all point-side parabolic markings.
No second/third model identification is an input to this theorem. -/
theorem source_single_a5_j3_point_parabolics_of_four
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
          ∃ (L12 : Subgroup G) (f s : G),
            L12 ≤ j.range ∧ f ∈ L12 ∧ orderOf f = 2 ∧ s ∈ L12 ∧ orderOf s = 3 ∧
            Commute s f ∧ j.range ⊓ second L12 = L12 ∧
            Nonempty (j.range ≃* Sporadic.Janko3.SourceRecognition.Seventeen.Plane ⋊[pointAction]
              Complement) ∧
            centralizer (pCore 2 j.range : Set j.range) = pCore 2 j.range ∧
            Nonempty (L12 ≃* Complement) ∧
            second L12 ≤ normalizer (zpowers s : Set G) ∧
            j.range ⊓ third j.range L12 f = j.range ⊓ centralizer ({f} : Set G) ∧
            second L12 ⊓ third j.range L12 f = second L12 ⊓ centralizer ({f} : Set G) := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨_,_,C,_,a,_,_,j,hj⟩ := hfields A hA
  exact ⟨C,a,j,hj,Janko23.J3Recognition.Ambient.BaumeisterParabolics.point_marking j hj.1⟩

/-- The first/third overlap in both original terminal planes, with its actual
chosen involution. The pair overlap is also supplied as soon as Lemma 2.5
identifies the same actual normalizer; no centralizer map is assumed. -/
theorem source_single_a5_j3_parabolic_overlaps_of_four
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
          Nonempty ((j.range ⊓ third j.range (overlap j) (j fieldElement) : Subgroup G) ≃*
            (alternatingGroup (Fin 4) × Multiplicative (ZMod 2))) ∧
          (Nonempty (second (overlap j) ≃* PairGroup) →
            Nonempty ((second (overlap j) ⊓ third j.range (overlap j) (j fieldElement) :
              Subgroup G) ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)))) := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨_,_,C,_,a,_,_,j,hj⟩ := hfields A hA
  refine ⟨C,a,j,hj,
    ⟨Janko23.J3Recognition.Ambient.BaumeisterParabolics.overlap13Equiv j hj.1⟩,?_⟩
  rintro ⟨hpair⟩
  exact ⟨Janko23.J3Recognition.Ambient.BaumeisterParabolics.overlap23Equiv j hj.1 hpair⟩

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
