module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CubicProjective
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicNormalizer

/-!
# The PGL₂(9) quotient in the original terminal J₃ row

For the same central cubic in each previously selected plane complement,
the full ambient normalizer modulo that cubic is the actual PGL₂(9)
model. An involution inverts this cubic and complements its centralizer;
its quotient image supplements the literal embedded A₆. The order-eight
witness is retained in the quotient.

The complete original terminal prefix supplies every premise. Both planes,
the returning pair and the original core/component identifications are
preserved. Splitting over the cubic itself, the compatible amalgam,
ambient recognition and the terminal solvability conclusion remain open.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), Lemma 2.4,
p.495; Aschbacher–Smith I.4.7(2) and 14.3.15, pp.418,994.
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

open Janko23.J3Recognition.Ambient

/-- The projective quotient and involutory supplement for the same cubic in each original plane. -/
theorem source_single_a5_j3_cubic_projective_quotients_of_four
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
        ∃ (C : Subgroup (normalizer (A : Set G))) (s : C),
          (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
          Nat.card C = 180 ∧ s ∈ center C ∧ orderOf s = 3 ∧
          let u : G := ((s : normalizer (A : Set G)) : G)
          Nonempty ((centralizer ({u} : Set G) ⧸ cubicKernel u) ≃*
            alternatingGroup (Fin 6)) ∧
          center (centralizer ({u} : Set G)) = cubicKernel u ∧
          Nat.card (centralizer ({u} : Set G)) = 1080 ∧
          Nat.card (normalizer (zpowers u : Set G)) = 2160 ∧
          Nat.card (normalizer (zpowers u : Set G) ⧸ cubicNormalizerKernel u) = 720 ∧
          (cubicQuotientInclusion u).range.index = 2 ∧
          _root_.commutator (normalizer (zpowers u : Set G) ⧸ cubicNormalizerKernel u) =
            (cubicQuotientInclusion u).range ∧
          Nonempty ((normalizer (zpowers u : Set G) ⧸ cubicNormalizerKernel u) ≃*
            GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) ∧
          ∃ r : normalizer (zpowers u : Set G), orderOf r = 2 ∧
            (r : G) * u * (r : G)⁻¹ = u⁻¹ ∧
            ((centralizer ({u} : Set G)).subgroupOf (normalizer (zpowers u : Set G))).IsComplement'
              (zpowers r) ∧
            let q := QuotientGroup.mk' (cubicNormalizerKernel u)
            orderOf (q r) = 2 ∧ (cubicQuotientInclusion u).range ⊔ zpowers (q r) = ⊤ ∧
            ∃ x : normalizer (zpowers u : Set G) ⧸ cubicNormalizerKernel u, orderOf x = 8 := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hquot⟩ :=
    source_single_a5_j3_cubic_normalizers_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨C,s,hC,hcardC,hsc,hs,⟨eC⟩,hcenter,hCc,hNc,hQc,hindex,hderived,_⟩ := hquot A hA
  have hsG : orderOf ((s : normalizer (A : Set G)) : G) = 3 :=
    (orderOf_coe (s : normalizer (A : Set G))).trans ((orderOf_coe s).trans hs)
  obtain ⟨r,hr,hri,hqr,hgen,x,hx⟩ := cubic_normalizer_quotient_actors P hc _ hsG eC
  exact ⟨C,s,hC,hcardC,hsc,hs,⟨eC⟩,hcenter,hCc,hNc,hQc,hindex,hderived,
    cubic_normalizer_quotient_pgl_nine P hc _ hsG eC,r,hr,hri,
    cubic_normalizer_involution_complement D.localType hc _ hsG eC r hr hri,
    hqr,hgen,x,hx⟩

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
