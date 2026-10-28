module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicNormalizerIntersection
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorConjugacySolvable
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The centralizer supplement of the quaternion closure

The original two-core is the product of the quaternion closure with its
centralizer. On either marked elementary factor, the centralizer fixes its
intersection with the closure and every commutator lies in the marked point.
The commutator calculation uses the literal intersection of the two local
cores, so it precedes any classification of the action on the factor.
Source: Aschbacher--Smith, Quasithin Groups, 14.3.19(1)--(2), printed p.997.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem factor_supplement_commutator_le_center
    {T : Sylow 2 G} {V : Subgroup G} {n : ℕ} (F : InvariantFlag T V n)
    (R A : Subgroup G) (hRH : R≤F.H)
    (hRQ : R⊓F.H.pCoreIn 2=F.W) (hAR : A≤R)
    (hQA : F.H.pCoreIn 2≤normalizer (A:Set G)) :
    ⁅A,F.H.pCoreIn 2⊓centralizer (F.U:Set G)⁆≤F.ZU ∧
      F.H.pCoreIn 2⊓centralizer (F.U:Set G)≤centralizer (A⊓F.U:Set G) := by
  let Q:=F.H.pCoreIn 2
  let D:=Q⊓centralizer (F.U:Set G)
  have hHQ : F.H≤normalizer (Q:Set G) := F.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  have hHD : F.H≤normalizer (D:Set G) :=
    (le_inf hHQ ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer F.U))).trans inf_normalizer_le_normalizer_inf
  have hAD : A≤normalizer (D:Set G) := (hAR.trans hRH).trans hHD
  have hDA : D≤normalizer (A:Set G) := inf_le_left.trans hQA
  have hcommA : ⁅A,D⁆≤A := le_normalizer_iff_commutator_le_left.mp hDA
  have hcommD : ⁅A,D⁆≤D := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hAD
  have hcommR : ⁅A,D⁆≤R⊓Q := le_inf (hcommA.trans hAR) (hcommD.trans inf_le_left)
  have hcommU : ⁅A,D⁆≤F.U := by
    rw [hRQ] at hcommR
    exact hcommR.trans inf_le_left
  constructor
  · change ⁅A,D⁆≤F.ZU
    rw [ZU,centerIn_eq_inf_centralizer]
    exact le_inf hcommU (hcommD.trans inf_le_right)
  · exact inf_le_right.trans (centralizer_le inf_le_right)

theorem source_factor_supplement_of_full_orthogonal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (dg : ClosureGeometry F) (hZ : F.ZU=F.Vi 1) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization F.terminalRepresentation ⊤) :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let Q := F.H.pCoreIn 2
    let D := Q⊓centralizer (F.U:Set G)
    Q=F.U⊔D ∧ ∃ A : Subgroup G,
      A≤R ∧ rankTwoSeed T M≤A ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16 ∧
      F.I₂ (sourceResidual M Mc)⊔Q≤normalizer (A:Set G) ∧
      ⁅A,D⁆≤F.Vi 1 ∧ D≤centralizer (A⊓F.U:Set G) := by
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q := F.H.pCoreIn 2
  obtain ⟨A,B,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hs,hRc,hAN,hBN⟩ :=
    elementary_factors_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
      F dg hZ hne g hgP hgH hr
  have hRT := (parabolic_core_sylow_index_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hRQ := (parabolic_core_intersection_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hf := factor_supplement_commutator_le_center F R A
    (hRT.trans (F.invariant 1)) hRQ hAR (le_sup_right.trans hAN)
  rw [hZ] at hf
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  exact ⟨core_eq_U_sup_centralizer F dg hZ dU,A,hAR,hVA,hEA,hAc,hAN,hf⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
