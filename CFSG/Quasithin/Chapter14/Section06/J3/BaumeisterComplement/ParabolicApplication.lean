module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.FieldSplitting
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.BaumeisterParabolics

/-!
# Literal Baumeister normalizers in the original terminal J₃ row

For each original plane, retain its actual field-affine embedding. Its
selected cubic has an A₆ centralizer quotient and a PGL₂(9) complement
in its normalizer, with the marking given by the original quotient map.
The same embedding supplies L₁ ∩ L₂ = L₁₂, C_G(s) ∩ L₂ = L₁₂,
|L₂| = 60, and the literal first/third intersection A₄ × C₂.

This applies the completed quotient and splitting calculations to the
full original terminal hypotheses and both plane orientations. The
S₃ × D₁₀ identification of L₂ and the A₅ × C₂ identification of L₃
remain required to construct OriginalMarking; neither is assumed here.

Sources: Baumeister, A geometry for groups of J₃-type (2007), 2.4–2.6,
pp.495–496; Aschbacher–Smith I.4.7(2), 14.3.15.
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

/-- The literal field parabolics in both original terminal planes: same-cubic
splitting, the centralizer and point intersections, and order sixty for L₂.
The S₃ × D₁₀ and A₅ × C₂ identifications remain necessary for OriginalMarking. -/
theorem source_single_a5_j3_literal_parabolics
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
          let s := j cubic
          Nonempty ((centralizer ({s} : Set G) ⧸ Janko23.J3Recognition.Ambient.cubicKernel s) ≃*
            alternatingGroup (Fin 6)) ∧
          centralizer ({s} : Set G) ⊓ second (overlap j) = overlap j ∧
          Nat.card (second (overlap j)) = 60 ∧
          j.range ⊓ second (overlap j) = overlap j ∧
          Nonempty ((j.range ⊓ third j.range (overlap j) (j fieldElement) : Subgroup G) ≃*
            (alternatingGroup (Fin 4) × Multiplicative (ZMod 2))) ∧
          ∃ (L : Subgroup (normalizer (zpowers s : Set G)))
            (eQ : (normalizer (zpowers s : Set G) ⧸
              Janko23.J3Recognition.Ambient.cubicNormalizerKernel s) ≃*
              GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
            (eL : L ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F),
            (Janko23.J3Recognition.Ambient.cubicNormalizerKernel s).IsComplement' L ∧
            ∀ x : L, eL x = eQ (QuotientGroup.mk'
              (Janko23.J3Recognition.Ambient.cubicNormalizerKernel s) x.val) := by
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
  obtain ⟨e6⟩ := Janko23.J3Recognition.Ambient.BaumeisterComplement.field_cubic_quotient (z := D.z)
    D.localType hc j hj.1
  refine ⟨C,a,j,hj,⟨e6⟩,
    Janko23.J3Recognition.Ambient.BaumeisterComplement.field_overlap_centralizer_intersection j hj.1 e6,
    Janko23.J3Recognition.Ambient.BaumeisterComplement.field_pair_card (z := D.z) D.localType hc j hj.1,
    point_intersection_normalizer j hj.1,
    ⟨Janko23.J3Recognition.Ambient.BaumeisterParabolics.overlap13Equiv j hj.1⟩,?_⟩
  exact Janko23.J3Recognition.Ambient.BaumeisterComplement.field_cubic_normalizer_complement P hc A hcardA hAR j hj.1

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
