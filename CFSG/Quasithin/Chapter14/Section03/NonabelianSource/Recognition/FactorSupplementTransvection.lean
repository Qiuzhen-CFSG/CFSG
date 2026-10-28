module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorSupplementAction
public import Theory.GroupAction.CommonAxisDichotomy

/-!
# The exact nontrivial supplement action on the original factor

If the centralizer supplement acts nontrivially on the elementary factor,
its image has order two, its commutator subgroup is the marked point, and
its nonidentity actor fixes exactly the intersection with the quaternion
closure. These are the literal axis and center in source14.3.19(2)(ii).
The trivial branch is retained; its dihedral Sylow automizer is a separate
part of the source normalizer calculation.
Source: Aschbacher--Smith, 14.3.19(2), printed p.997.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
theorem source_factor_supplement_transvection_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot) :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    let Q := F.H.pCoreIn 2
    let D := Q⊓centralizer (F.U:Set G)
    Q=F.U⊔D ∧ ∃ A : Subgroup G,
      A≤R ∧ rankTwoSeed T M≤A ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16 ∧
      Nat.card (A⊓F.U:Subgroup G)=8 ∧
      ∃ hAN : F.I₂ (sourceResidual M Mc)⊔Q≤normalizer (A:Set G),
      (D≤centralizer (A:Set G) ∨
       (Nat.card (A.normalizerMonoidHom.comp
         (inclusion (show D≤normalizer (A:Set G) from
           inf_le_left.trans (le_sup_right.trans hAN)))).range=2 ∧
        ⁅A,D⁆=F.Vi 1 ∧ ∀d:G,d∈D→d∉centralizer (A:Set G)→
          ∀a:G,a∈A→(Commute d a ↔ a∈A⊓F.U))) := by
  obtain ⟨hQ,A,hAR,hVA,hEA,hAc,hAU,hAN,hcomm,hfix,_⟩ :=
    source_factor_supplement_action_of_solvable hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hs
  refine ⟨hQ,A,hAR,hVA,hEA,hAc,hAU,hAN,?_⟩
  exact conjugation_dichotomy_of_fixed_hyperplane A
    (F.H.pCoreIn 2⊓centralizer (F.U:Set G)) (A⊓F.U) (F.Vi 1)
    (inf_le_left.trans (le_sup_right.trans hAN)) inf_le_left ((F.le_seed 1).trans hVA)
    hAc hAU (by simpa using F.card 1 (by decide)) hfix hcomm
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
