module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CommonComplements
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3PlaneNatural

/-!
# Common overlap complements in the original terminal J₃ row

The complete original terminal prefix constructs the actual H-type seed,
returning pair and root marking. The two natural normalizer complements
can now be chosen to intersect in a common subgroup S of order nine,
with R S equal to the whole overlap. The field-affine embeddings use
these same complements; their translation maps agree on the original E,
and their field involutions retain the exact fourth-power action.

This application adds no source hypothesis. The ambient opposite-root and
Weyl construction, generation and presentation comparison are still needed
for J₃ recognition. The independent EightImageRow exclusion and terminal
solvability are not asserted here.

Sources: Aschbacher–Smith 14.3.15 and I.4.7(2), pp.994,418;
Aschbacher, *Sporadic Groups* (1994), 46.14(1–5a), pp.257–258.
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

open Sporadic.Janko3.SourceRecognition.PlaneCoordinates
open Sporadic.Janko3.SourceRecognition.PlaneTransport

/-- Shared actual complements and compatible field roots from the full
original selected terminal prefix, preserving the component and centralizer. -/
theorem source_single_a5_j3_common_complements_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Janko23.OneInvolutionClass G ∧
    ∃ (D : Seed G) (P : ReturningPair D)
      (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root),
      F.H = K ∧ F.H = Janko23.involutionCentralizer D.z ∧
      Janko23.ambientCore D.z = F.U ∧
      P.A₁ eR ≠ P.A₂ eR ∧ P.A₁ eR ⊔ P.A₂ eR = P.R ∧ P.A₁ eR ⊓ P.A₂ eR = P.E ∧
      Nat.card (normalizer (P.A₁ eR : Set G) ⊓ normalizer (P.A₂ eR : Set G) : Subgroup G) = 576 ∧
    ∃ (S : Subgroup G)
      (C₁ : Subgroup (normalizer (P.A₁ eR : Set G)))
      (f₁ : C₁ ≃* LinearGroup) (a₁ : P.A₁ eR ≃* Plane)
      (j₁ : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G)
      (C₂ : Subgroup (normalizer (P.A₂ eR : Set G)))
      (f₂ : C₂ ≃* LinearGroup) (a₂ : P.A₂ eR ≃* Plane)
      (j₂ : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G),
      Nat.card S = 9 ∧
      Disjoint P.R S ∧
      P.R ⊔ S = normalizer (P.A₁ eR : Set G) ⊓ normalizer (P.A₂ eR : Set G) ∧
      ((P.A₁ eR).subgroupOf (normalizer (P.A₁ eR : Set G))).IsComplement' C₁ ∧
      (∀ (c : C₁) (x : P.A₁ eR),
        a₁ ((P.A₁ eR).normalizerMonoidHom c x) = naturalAction (f₁ c) (a₁ x)) ∧
      FieldEmbedding (P.A₁ eR) C₁ a₁ j₁ ∧
      ((P.A₂ eR).subgroupOf (normalizer (P.A₂ eR : Set G))).IsComplement' C₂ ∧
      (∀ (c : C₂) (x : P.A₂ eR),
        a₂ ((P.A₂ eR).normalizerMonoidHom c x) = naturalAction (f₂ c) (a₂ x)) ∧
      FieldEmbedding (P.A₂ eR) C₂ a₂ j₂ ∧
      C₁.map (normalizer (P.A₁ eR : Set G)).subtype ⊓
        C₂.map (normalizer (P.A₂ eR : Set G)).subtype = S ∧
      (∀ (x : G) (hx₁ : x ∈ P.A₁ eR) (hx₂ : x ∈ P.A₂ eR),
        a₁ ⟨x,hx₁⟩ = a₂ ⟨x,hx₂⟩) ∧
      j₁.comp baseRoot = j₂.comp baseRoot ∧ (j₁.comp baseRoot).range = P.E ∧
      j₁ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∈ P.A₂ eR ∧
      j₁ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∉ P.A₁ eR ∧
      j₂ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∈ P.A₁ eR ∧
      j₂ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∉ P.A₂ eR := by
  obtain ⟨hc,D,P,eR,_,_,hHK,hHz,hcore,_⟩ :=
    source_single_a5_j3_local_sixteen_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  exact ⟨hc,D,P,eR,hHK,hHz,hcore,P.planes_ne eR,P.planes_sup eR,P.planes_inf eR,
    Janko23.J3Recognition.Ambient.overlap_card P eR,
    Janko23.J3Recognition.Ambient.compatible_fields_with_common_complement P hc eR⟩

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
