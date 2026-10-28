module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.PlaneAction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3LocalSixteen

/-!
# Sylow exhaustion, fusion and full plane-normalizer orders in the original terminal branch

The original terminal construction supplies the one-class J₃ local system,
using completed J₂ recognition to exclude the other branch. Its actual
order-128 Sylow has exactly two elementary sixteen-groups. Their full ambient
normalizers control fusion, are transitive on the nonidentity points, have
order 2880, and act faithfully modulo the original plane with image order
180. Their common root stabilizers have index five.

Every local premise in this application is discharged from the original
terminal prefix. The literal GL₂(4) quotient/action marking, splitting,
ambient J₃ recognition and exact L₂(8) exclusion remain subsequent source
obligations; these order and fusion results do not assert them.

Sources: Aschbacher–Smith 14.3.15 and I.4.7, pp.994,418;
Aschbacher, *Sporadic Groups* (1994), 46.14(2,4,5a), pp.257–258.
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

/-- The actual original terminal planes, with Sylow exhaustion and full normalizer data. -/
theorem source_single_a5_j3_plane_normalizer_orders_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Janko23.OneInvolutionClass G ∧
    ∃ (D : Seed G) (P : ReturningPair D)
      (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) (S : Sylow 2 G),
      F.H = K ∧ F.H = Janko23.involutionCentralizer D.z ∧
      Janko23.ambientCore D.z = F.U ∧
      P.R ≤ (S : Subgroup G) ∧ (S : Subgroup G) ≤ normalizer (P.R : Set G) ∧
      Nat.card S = 128 ∧ Nat.card P.R = 64 ∧
      P.A₁ eR ≠ P.A₂ eR ∧ P.A₁ eR ⊔ P.A₂ eR = P.R ∧ P.A₁ eR ⊓ P.A₂ eR = P.E ∧
      (∀ A : Subgroup G, A ≤ (S : Subgroup G) → IsElementaryAbelian 2 A → Nat.card A ≤ 16) ∧
      (∀ A : Subgroup G, A ≤ (S : Subgroup G) →
        ((IsElementaryAbelian 2 A ∧ Nat.card A = 16) ↔ A = P.A₁ eR ∨ A = P.A₂ eR)) ∧
      (∀ A : Subgroup G, A = P.A₁ eR ∨ A = P.A₂ eR →
        IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
        A ⊓ F.U = P.E ∧ centralizer (A : Set G) = A ∧
        Nat.card (normalizer (A : Set G)) = 2880 ∧
        A.normalizerMonoidHom.ker = A.subgroupOf (normalizer (A : Set G)) ∧
        Nat.card A.normalizerMonoidHom.range = 180 ∧
        (normalizer (P.R : Set G)).relIndex (normalizer (A : Set G)) = 5 ∧
        (∀ x ∈ A, ∀ y ∈ A, IsConj x y →
          ∃ n ∈ normalizer (A : Set G), MulAut.conj n x = y) ∧
        (∀ x ∈ A, ∀ y ∈ A, x ≠ 1 → y ≠ 1 →
          ∃ n ∈ normalizer (A : Set G), MulAut.conj n x = y) ∧
        ∃ n ∈ normalizer (A : Set G),
          MulAut.conj n D.z ∉ P.E ∧ n ∉ normalizer (P.R : Set G)) := by
  obtain ⟨hc,D,P,eR,_,S,hHK,hHz,hcore,hRS,hSN,hS,hR,_,_,_,_,_,_,_,hneP,hjoin,hinf,_,_⟩ :=
    source_single_a5_j3_local_sixteen_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,S,hHK,hHz,hcore,hRS,hSN,hS,hR,hneP,hjoin,hinf,?_,
    P.elementary_sixteen_in_sylow_iff eR S hRS hSN hS,?_⟩
  · intro A hAS hAe
    let : IsElementaryAbelian 2 A := hAe
    exact P.elementary_sylow_card_le_sixteen S hRS hSN hS A hAS
  · intro A hA
    have hAR : A ≤ P.R := by
      rcases hA with rfl | rfl
      · exact P.A₁_le_R eR
      · exact P.A₂_le_R eR
    have hEA : P.E ≤ A := by
      rw [←hinf]
      rcases hA with rfl | rfl
      · exact inf_le_left
      · exact inf_le_right
    have he := (P.elementary_sixteen_iff eR A hAR).mpr hA
    let : IsElementaryAbelian 2 A := he.1
    refine ⟨he.1,he.2,?_,P.plane_centralizer A he.2 hAR,
      P.plane_normalizer_card hc A he.2 hAR,P.plane_normalizer_action_kernel A he.2 hAR,
      P.plane_normalizer_action_card hc A he.2 hAR,
      P.root_stabilizer_index_in_plane_normalizer hc A he.2 hAR,?_,?_,
      P.plane_normalizer_escapes hc A he.2 hEA⟩
    · rw [←hcore]
      exact P.plane_inf_core A hAR hEA
    · intro x hx y hy hxy
      exact P.elementary_sixteen_normalizer_fusion hc A he.2 x y hx hy hxy
    · intro x hx y hy hx1 hy1
      exact P.elementary_sixteen_normalizer_transitive hc A he.2 x y hx hy hx1 hy1

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
