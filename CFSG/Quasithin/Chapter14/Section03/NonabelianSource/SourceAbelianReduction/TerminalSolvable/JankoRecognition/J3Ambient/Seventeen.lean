module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.Seventeen
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.Seventeen.Recognition
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.FieldSubgroups

/-!
# The seventeen-point coset-graph construction in the original terminal row

The original terminal prefix supplies the field-affine subgroup in each
selected plane normalizer. For that literal subgroup L₁, the genuine
Baumeister markings of L₁₂, N_G(L₁₂) and the generated involution-centralizer
subgroup give a complete faithful coset graph of valency sixteen and a
triply transitive degree-seventeen action of the order-8160 completion.

The markings in `OriginalMarking` remain explicit preceding-source inputs,
owned by the ambient-recognition task. They are not extracted from plane
data. Lemma 2.9 supplies simultaneous embedding uniqueness and the marked
completion comparison below. The actual marked model now discharges
Corollary 2.10: the terminal-row completion is PSL₂(16):2 with its selected
involution carried to fourth-power Frobenius.
This result asserts no terminal solvability or full J₃ recognition and
retains the original full KnownSimple/proper-K hypotheses.

Sources: Baumeister, *A geometry for groups of J₃-type* (2007),
pp.496–498; Aschbacher–Smith I.4.7(2), 14.3.15, pp.418,994.
-/

public noncomputable section
open Subgroup MulAction Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
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

/-- The graph construction applies to the actual field-affine subgroup in each
original plane once Lemmas 2.5–2.6 and the literal intersections are supplied. -/
theorem source_single_a5_j3_coset_graphs_of_four
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
          ∀ (L12 : Subgroup G) (f : G) (mark : OriginalMarking j.range L12 f),
            ∃ (b : completion j.range L12) (hb : b * b = 1) (hbout : (b : G) ∉ j.range),
              (b : G) ∈ second L12 ∧ (b : G) ∈ third j.range L12 f ∧
              let d := mark.localSource.cosetData b hb hbout
              (CosetGraph.graph d).Connected ∧
                FaithfulSMul (completion j.range L12) (CosetGraph.Vertex d) ∧
                (∀ x : CosetGraph.Vertex d,
                  Nat.card ((CosetGraph.graph d).neighborSet x) = 16) ∧
                CosetGraph.NeighborTwoTransitive d := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨_,_,C,_,a,_,_,j,hj⟩ := hfields A hA
  exact ⟨C,a,j,hj,fun _ _ mark => mark.exists_graph_properties⟩

/-- Lemma 2.7 applies to the literal field-affine subgroup supplied by the terminal row,
with the source normalizer and centralizer markings retained as earlier-source inputs. -/
theorem source_single_a5_j3_seventeen_action_of_four
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
          ∀ (L12 : Subgroup G) (f : G) (mark : OriginalMarking j.range L12 f),
            ∃ (b : completion j.range L12) (hb : b * b = 1) (hbout : (b : G) ∉ j.range),
              (b : G) ∈ second L12 ∧ (b : G) ∈ third j.range L12 f ∧
              let d := mark.localSource.cosetData b hb hbout
              FaithfulSMul (completion j.range L12) (CosetGraph.Vertex d) ∧
                (CosetGraph.graph d).Connected ∧ CosetGraph.graph d = ⊤ ∧
                (∀ x : CosetGraph.Vertex d,
                  Nat.card ((CosetGraph.graph d).neighborSet x) = 16) ∧
                Nat.card (CosetGraph.Vertex d) = 17 ∧
                IsMultiplyPretransitive (completion j.range L12) (CosetGraph.Vertex d) 3 ∧
                Nat.card (completion j.range L12) = 8160 ∧
                stabilizer (completion j.range L12) (CosetGraph.base d) =
                  j.range.subgroupOf (completion j.range L12) ∧
                stabilizer (completion j.range L12)
                  ({CosetGraph.base d, CosetGraph.other d} : Set (CosetGraph.Vertex d)) =
                  (second L12).subgroupOf (completion j.range L12) := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨_,_,C,_,a,_,_,j,hj⟩ := hfields A hA
  exact ⟨C,a,j,hj,fun _ _ mark => mark.exists_seventeen_action⟩

/-- Lemma 2.9 compares the literal terminal-row completion with any second
source completion, preserving both local groups and the marked involution.
The constructed PSL₂(16):2 model supplies the specialization below. -/
theorem source_single_a5_j3_marked_completion_comparison_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    {J : Type*} [Group J] (N : SourceData J)
    (t : J) (ht : t ∈ N.H1 ⊓ N.H2) (hot : orderOf t = 2) :
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
          ∀ (L12 : Subgroup G) (f : G) (mark : OriginalMarking j.range L12 f),
            ∃ e : completion j.range L12 ≃* J,
              (j.range.subgroupOf (completion j.range L12)).map e.toMonoidHom = N.H1 ∧
              ((second L12).subgroupOf (completion j.range L12)).map e.toMonoidHom = N.H2 ∧
              e mark.involutionInCompletion = t := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨_,_,C,_,a,_,_,j,hj⟩ := hfields A hA
  exact ⟨C,a,j,hj,fun _ _ mark => mark.completion_equiv_preserving_involution N t ht hot⟩

/-- Corollary 2.10 on the literal terminal-row completion. All model clauses
are discharged, and the original involution is marked as fourth-power Frobenius.
The original preceding-source markings remain with their ambient owner. -/
theorem source_single_a5_j3_marked_psl2_sixteen_of_four
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
          ∀ (L12 : Subgroup G) (f : G) (mark : OriginalMarking j.range L12 f),
            ∃ e : completion j.range L12 ≃* Theory.PSL2.BinaryFourFieldExtension.Model,
              (j.range.subgroupOf (completion j.range L12)).map e.toMonoidHom = ModelAmalgam.point ∧
              ((second L12).subgroupOf (completion j.range L12)).map e.toMonoidHom = ModelAmalgam.pair ∧
              ((third j.range L12 f).subgroupOf (completion j.range L12)).map e.toMonoidHom =
                ModelAmalgam.Triangle ∧
              e mark.involutionInCompletion = Theory.PSL2.BinaryFourFieldExtension.involution := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hfields⟩ :=
    source_single_a5_j3_field_subgroups_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨_,_,C,_,a,_,_,j,hj⟩ := hfields A hA
  exact ⟨C,a,j,hj,fun _ _ mark => mark.recognition⟩

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
