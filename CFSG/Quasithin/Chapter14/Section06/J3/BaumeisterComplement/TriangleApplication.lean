module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.Triangle
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.PairApplication
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.Seventeen

/-!
# Third-parabolic quotient and central splitting on both original planes

For each original plane, the literal third parabolic surjects onto the
A₅ quotient of its involution centralizer. The original marking follows
from the one remaining kernel equality L₃ ∩ Q_f = ⟨f⟩; the A₅ × C₂
model and all overlap maps are then constructed, not supplied as inputs.
The final consumer applies marked Corollary 2.10 with the same subgroup
images and involution. This is an application of the quotient and central-splitting increment,
not a discharge of Baumeister's simultaneous complement alignment.

Sources: Baumeister (2007), Lemmas 2.5–2.6, pp.496–497;
Aschbacher–Smith I.4.7(2), 14.3.15.
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

/-- Both original planes have the full A₅ third-parabolic quotient. The
remaining premise for OriginalMarking is precisely the intersection of the
GENERATED third group with the actual involution-centralizer two-core. -/
theorem source_single_a5_j3_third_quotients
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
          let f := j fieldElement
          let Cf := Janko23.involutionCentralizer f
          let L3 := third j.range (overlap j) f
          (L3.subgroupOf Cf).map (QuotientGroup.mk' (pCore 2 Cf)) = ⊤ ∧
          (L3 ⊓ (pCore 2 Cf).map Cf.subtype = zpowers f →
            Nonempty (OriginalMarking j.range (overlap j) f)) := by
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
  refine ⟨C,a,j,hj,
    Janko23.J3Recognition.Ambient.BaumeisterComplement.field_third_quotient
      P hc A hcardA hAR j hj.1,?_⟩
  intro hL3
  exact ⟨Janko23.J3Recognition.Ambient.BaumeisterComplement.field_original_marking_of_core_intersection
    P hc A hcardA hAR j hj.1 hL3⟩

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
open Sporadic.Janko3.SourceRecognition.Seventeen
open Seventeen
variable {G : Type*} [Group G] [Finite G]

/-- Apply the completed marked Corollary 2.10 to these same field subgroups.
Only the generated third-core intersection remains explicit; no model-map or
OriginalMarking premise is retained. -/
theorem field_marked_completion_of_core_intersection {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (j : Model →* G) (hj : Function.Injective j)
    (hcore : third j.range (overlap j) (j fieldElement) ⊓
      (pCore 2 (involutionCentralizer (j fieldElement))).map
        (involutionCentralizer (j fieldElement)).subtype = zpowers (j fieldElement)) :
    ∃ (mark : OriginalMarking j.range (overlap j) (j fieldElement))
      (e : completion j.range (overlap j) ≃* Theory.PSL2.BinaryFourFieldExtension.Model),
      (j.range.subgroupOf (completion j.range (overlap j))).map e.toMonoidHom =
        ModelAmalgam.point ∧
      ((second (overlap j)).subgroupOf (completion j.range (overlap j))).map e.toMonoidHom =
        ModelAmalgam.pair ∧
      ((third j.range (overlap j) (j fieldElement)).subgroupOf
        (completion j.range (overlap j))).map e.toMonoidHom = ModelAmalgam.Triangle ∧
      e mark.involutionInCompletion = Theory.PSL2.BinaryFourFieldExtension.involution := by
  let mark := field_original_marking_of_core_intersection P hc A hA hAR j hj hcore
  exact ⟨mark,mark.recognition⟩

end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
