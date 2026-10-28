module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.Sylow
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J2Source

/-!
# The actual J₃ root pair in the original terminal branch

The original normalized A₅ branch supplies its actual involution centralizer
and minus-extraspecial core. The completed J₂ source theorem excludes the
two-class alternative using the original non-model hypothesis. The common
H-type construction then gives an ambient root group R, its full split
normalizer, both elementary sixteen-groups, and an ambient Sylow containing
R inside that normalizer. The normalizer isomorphism preserves the literal
root inclusion; neither of the original nonabelian cores is relabelled as
an elementary subgroup.

This proves the stated local construction under the original terminal
prefix. The larger normalizers of the sixteen-groups, ambient J₃ recognition,
and the independent exact L₂(8) exclusion remain required for terminal
solvability.

Sources: Aschbacher–Smith 14.3.15 and I.4.7, pp.994,418;
Aschbacher, *Sporadic Groups* (1994), 46.2–46.3 and 46.14, pp.251,257–258.
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

/-- A constructed and marked local system in the original source group.
All local geometry and normalizer premises are discharged. -/
theorem source_single_a5_j3_local_sixteen_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Janko23.OneInvolutionClass G ∧
    ∃ (D : Seed G) (P : ReturningPair D)
      (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root)
      (eN : normalizer (P.R : Set G) ≃* Matrix.PSL3Four.RootNormalizerModel.Model)
      (S : Sylow 2 G),
      F.H = K ∧ F.H = Janko23.involutionCentralizer D.z ∧
      Janko23.ambientCore D.z = F.U ∧
      P.R ≤ (S : Subgroup G) ∧ (S : Subgroup G) ≤ normalizer (P.R : Set G) ∧
      Nat.card S = 128 ∧ Nat.card P.R = 64 ∧
      Nat.card (normalizer (P.R : Set G)) = 1152 ∧
      centralizer (P.R : Set G) = P.E ∧
      (∀ r : P.R, eN (inclusion le_normalizer r) = SemidirectProduct.inl (eR r)) ∧
      IsElementaryAbelian 2 (P.A₁ eR) ∧ IsElementaryAbelian 2 (P.A₂ eR) ∧
      Nat.card (P.A₁ eR) = 16 ∧ Nat.card (P.A₂ eR) = 16 ∧
      P.A₁ eR ≠ P.A₂ eR ∧ P.A₁ eR ⊔ P.A₂ eR = P.R ∧
      P.A₁ eR ⊓ P.A₂ eR = P.E ∧
      ¬ P.A₁ eR ≤ F.U ∧ ¬ P.A₂ eR ≤ F.U := by
  obtain ⟨hHK,_,z,_,hHz,hcore,hz,htype⟩ := source_single_a5_janko_type_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hc : Janko23.OneInvolutionClass G := by
    rcases htype with h2 | h3
    · exact (hnot (JankoRecognition.source_j2_isTheoremEModel hG h2)).elim
    · exact h3.2
  let D : Seed G := ⟨z,hz⟩
  obtain ⟨P⟩ := exists_returningPair D
  obtain ⟨eR,eN,hmark⟩ := Geometry.Normalizer.exists_identification P
  obtain ⟨S,hRS,hSN,hScard⟩ := P.exists_ambient_sylow hc
  refine ⟨hc,D,P,eR,eN,S,hHK,hHz,hcore,hRS,hSN,hScard,P.R_card,
    Geometry.Normalizer.normalizer_R_card P,Geometry.centralizer_eq_E P,hmark,
    inferInstance,inferInstance,P.A₁_card eR,P.A₂_card eR,P.planes_ne eR,
    P.planes_sup eR,P.planes_inf eR,?_,?_⟩
  · rw [←hcore]
    exact P.A₁_not_le_core eR
  · rw [←hcore]
    exact P.A₂_not_le_core eR

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
