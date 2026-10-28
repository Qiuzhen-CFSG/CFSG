module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.FiveCosets
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3PlaneNormalizers

/-!
# Split plane normalizers and their five-coset actions in the original terminal branch

The original terminal prefix constructs the one-class J₃ local system and
its actual elementary sixteen-groups. The full ambient normalizers now
split over those planes. The complements have order 180 and are identified
with the literal conjugation image; the full semidirect-product marking
fixes each original plane element. The plane is exactly the two-core.

The common root stabilizer's normal core has order 48. The full plane
normalizer modulo this core is actually A₅. Its image in the plane automizer is central of order three.
Every premise of these local results is discharged below. The natural
GL₂(4) marking, ambient J₃ recognition, exact L₂(8) exclusion and final
unconditional terminal solvability remain separate obligations.

Sources: Aschbacher–Smith 14.3.15 and I.4.7, pp.994,418;
Aschbacher, *Sporadic Groups* (1994), 46.14(5a), p.258.
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

/-- The whole original plane normalizers split; their literal five-coset quotients are A₅. -/
theorem source_single_a5_j3_split_plane_normalizers_of_four
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
        pCore 2 (normalizer (A : Set G)) = A.subgroupOf (normalizer (A : Set G)) ∧
        (∃ (C : Subgroup (normalizer (A : Set G)))
          (f : C ≃* A.normalizerMonoidHom.range),
          (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧ Nat.card C = 180 ∧
          ∀ c : C, (f c : MulAut A) = A.normalizerMonoidHom c) ∧
        (∃ f : normalizer (A : Set G) ≃*
          A ⋊[A.normalizerMonoidHom.range.subtype] A.normalizerMonoidHom.range,
          ∀ a : A, f (inclusion le_normalizer a) = SemidirectProduct.inl a) ∧
        Nat.card (((normalizer (P.R : Set G)).subgroupOf (normalizer (A : Set G))).normalCore) = 48 ∧
        Nonempty (((normalizer (A : Set G)) ⧸
          ((normalizer (P.R : Set G)).subgroupOf (normalizer (A : Set G))).normalCore) ≃*
          alternatingGroup (Fin 5)) ∧
        (let C := (((normalizer (P.R : Set G)).subgroupOf (normalizer (A : Set G))).normalCore).map
            A.normalizerMonoidHom.rangeRestrict;
          Nat.card C = 3 ∧ C ≤ center A.normalizerMonoidHom.range) := by
  obtain ⟨hc,D,P,eR,_,_,hHK,hHz,hcore,_⟩ :=
    source_single_a5_j3_local_sixteen_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  refine ⟨hc,D,P,eR,hHK,hHz,hcore,P.planes_ne eR,P.planes_sup eR,P.planes_inf eR,?_⟩
  intro A hA
  have hAR : A ≤ P.R := by
    rcases hA with rfl | rfl
    · exact P.A₁_le_R eR
    · exact P.A₂_le_R eR
  have he := (P.elementary_sixteen_iff eR A hAR).mpr hA
  let : IsElementaryAbelian 2 A := he.1
  exact ⟨he.1,he.2,P.plane_normalizer_twoCore hc A he.2 hAR,
    P.plane_normalizer_marked_complement hc A he.2 hAR,
    P.plane_normalizer_semidirect hc A he.2 hAR,
    P.plane_five_coset_kernel_card hc A he.2 hAR,
    P.plane_five_coset_quotient hc A he.2 hAR,
    P.plane_automizer_central_cubic hc A he.2 hAR⟩

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
