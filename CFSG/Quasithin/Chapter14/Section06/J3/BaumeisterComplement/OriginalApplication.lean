module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.Source
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicProjective

/-!
# Cubic-kernel splitting in the original terminal J₃ row

Keep each actual plane complement and its selected central cubic from the
original terminal configuration. The independent cubic/nonfusion claim of
Baumeister 2.4 now supplies a complement in that SAME cubic normalizer,
marked as PGL₂(9) by the original quotient projection.

The final theorem discharges the local fusion input using the natural
plane action and proves unconditional splitting in both original planes.
All original terminal hypotheses and both plane orientations are retained.
The L₂/L₃ model identifications and OriginalMarking remain source obligations;
this module does not assert ambient J₃ recognition.

Sources: Baumeister (2007), Lemma 2.4, pp.495–496;
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

open Janko23.J3Recognition.Ambient

/-- Apply the source nonfusion-to-splitting argument to the same cubic selected
in each original plane. The explicit fusion premise remains to be discharged. -/
theorem source_single_a5_j3_cubic_complements_of_nonfusion
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
          (∀ σ : centralizer ({u} : Set G), orderOf σ = 3 →
            σ ∉ cubicKernel u → ¬ IsConj (σ : G) (u * (σ : G)) →
            ∃ (L : Subgroup (normalizer (zpowers u : Set G)))
              (eQ : (normalizer (zpowers u : Set G) ⧸ cubicNormalizerKernel u) ≃*
                GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
              (eL : L ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F),
              (cubicNormalizerKernel u).IsComplement' L ∧
              ∀ x : L, eL x = eQ (QuotientGroup.mk' (cubicNormalizerKernel u) x.val)) := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hquot⟩ :=
    source_single_a5_j3_cubic_projective_quotients_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨C,s,hC,hcardC,hsc,hs,⟨eC⟩,_⟩ := hquot A hA
  refine ⟨C,s,hC,hcardC,hsc,hs,⟨eC⟩,?_⟩
  intro σ hσ hσout hn
  have hsG : orderOf ((s : normalizer (A : Set G)) : G) = 3 :=
    (orderOf_coe (s : normalizer (A : Set G))).trans ((orderOf_coe s).trans hs)
  exact BaumeisterComplement.normalizer_complement_projective_of_cubic_nonfusion
    P hc _ hsG eC σ hσ hσout hn

/-- The original terminal row has complements to its SAME cubic kernels,
with both natural-plane orientations and the literal quotient maps retained.
No additional nonfusion, Sylow-abelianity or complement premise is required. -/
theorem source_single_a5_j3_cubic_complements
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
          ∃ (L : Subgroup (normalizer (zpowers u : Set G)))
            (eQ : (normalizer (zpowers u : Set G) ⧸ cubicNormalizerKernel u) ≃*
              GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F)
            (eL : L ≃* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F),
            (cubicNormalizerKernel u).IsComplement' L ∧
            ∀ x : L, eL x = eQ (QuotientGroup.mk' (cubicNormalizerKernel u) x.val) := by
  obtain ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,hquot⟩ :=
    source_single_a5_j3_cubic_projective_quotients_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,hneP,hsup,hinf,?_⟩
  intro A hA
  obtain ⟨C,s,hC,hcardC,hsc,hs,⟨eC⟩,_⟩ := hquot A hA
  refine ⟨C,s,hC,hcardC,hsc,hs,⟨eC⟩,?_⟩
  let _ : IsElementaryAbelian 2 A := by
    rcases hA with rfl | rfl <;> infer_instance
  have hcardA : Nat.card A = 16 := by
    rcases hA with rfl | rfl
    · exact P.A₁_card eR
    · exact P.A₂_card eR
  have hAR : A ≤ P.R := by
    rcases hA with rfl | rfl
    · exact P.A₁_le_R eR
    · exact P.A₂_le_R eR
  exact BaumeisterComplement.normalizer_complement_projective_of_plane_cubic
    P hc A hcardA hAR C hC s hsc hs eC

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
