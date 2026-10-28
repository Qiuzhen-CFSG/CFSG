module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterKernel
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterRank

/-!
# The literal four-dimensional U-image in H/W

The original rank theorem supplies a normal quotient kernel described by
commutator displacement. The frozen full central-quotient action has exactly
the same predicate and exactly kernel W, so the normal kernel is identified
with the original W. The genuine outer hypothesis then forces the original
U-image to have order four, while retaining the cubic J-image and its
commutator generation.

Source: Aschbacher--Smith, following12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original H/W quotient has p-core-free literal action, original
U-image of order four, and the original cubic J-image generates it by
commutators. -/
theorem original_tripleSix_central_closure_outer_image_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let V1 := tripleSixPoint D a z
    let W := conjugateSpanBy V1 R
    ∃ (N : Subgroup H) (hN : N.Normal),
      letI := hN
      N = W.subgroupOf H ∧ pCore 2 (H ⧸ N) = ⊥ ∧
      let A := (U.subgroupOf H).map (QuotientGroup.mk' N)
      let Jstar := (J.subgroupOf H).map (QuotientGroup.mk' N)
      Nat.card A = 4 ∧ A = ⁅A, Jstar⁆ ∧
      Nat.card (Jstar ⧸ pCore 2 Jstar) = 3 := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨_, _, _, hN, _, _, _, hker, hk, hNcore, _, _⟩ :=
    original_tripleSix_central_closure_outer_kernel
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  obtain ⟨N, hNN, hmem, hcore, _, _, _, _, hgen, hJcard, hlast⟩ :=
    original_tripleSix_central_closure_outer_rank h structural D a z hz hzT hnot
  let : N.Normal := hNN
  obtain ⟨hWT, _, _, _, _, hcenter, hex, _⟩ :=
    original_tripleSix_central_closure_outer_extraspecial
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let : IsExtraspecial 2 W := hex
  have hWH : W ≤ H := hWT.trans le_sup_right
  have hclass : _root_.commutator W ≤ center W :=
    (IsExtraspecial.quotient_elementary_abelian 2 W).commutator_le_center_of_central_quotient
  have hNW : W.subgroupOf H ≤ N := by
    intro w hw
    have hp : ∀ x ∈ W, ⁅x, (w:G)⁆ ∈ Z := by
      intro x hx
      apply hcenter.le
      have hm := mem_map_of_mem W.subtype
        (hclass (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup W))
          (H₂ := (⊤ : Subgroup W)) (show (⟨x, hx⟩ : W) ∈ (⊤ : Subgroup W) from mem_top _)
          (show (⟨(w:G), hw⟩ : W) ∈ (⊤ : Subgroup W) from mem_top _)))
      change ⁅x, (w:G)⁆ ∈ (center W).map W.subtype at hm
      exact hm
    exact (hmem w).mpr hp
  have hWN : N ≤ W.subgroupOf H := by
    intro x hx
    have hp := (hmem x).mp hx
    have hxφ := (hker x).mpr hp
    exact hk.symm ▸ hxφ
  have hNW_eq : N = W.subgroupOf H := le_antisymm hWN hNW
  have hAcard4 : Nat.card ((U.subgroupOf H).map (QuotientGroup.mk' N)) = 4 :=
    Or.resolve_left hlast houter
  exact ⟨N, hNN, hNW_eq, hcore, hAcard4, hgen, hJcard⟩

end CFSG.Quasithin.Chapter12.Section07
