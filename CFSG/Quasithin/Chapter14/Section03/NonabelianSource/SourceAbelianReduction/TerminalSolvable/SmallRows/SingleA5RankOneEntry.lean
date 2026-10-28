module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5Kernel
public import CFSG.Quasithin.Chapter14.Section02.NormalF11
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors

/-!
# The original rank-one amalgam for a normalized terminal A₅

The literal normal component K in H=KT is the embedded two-residual of H.
Its A₅ two-core quotient is a concrete PSL₂(4), so the original normal
Bender construction applies on this same carrier. Transporting back from
K as a subgroup of H supplies all six F.1.1 clauses on the actual pair
(K,YS₂), where Y is the original residual and S₂=O₂(Y)(T intersection K).
The two Borel identities, Y=[Y,S₂] and the actual S₃ quotient of YS₂ are
retained. No containment T≤K is used.

The terminal application discharges the component kernel and quotient
using the checked numerical-branch comparison. Only the independently
produced large-actor alternatives remain in that application. These are
source inputs to the field-four recognition; neither the full two-core
identification nor the A₅ Borel contradiction is asserted here.

Source: Aschbacher--Smith 14.2.8(1), 14.2.11--16 and F.1.1, printed
pp.983--986 and 259; the normalized A₅ branch of14.3.15, p.994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

private theorem five_rankOne {A : Type*} [Group A]
    (e : A ≃* alternatingGroup (Fin 5)) : ChapterF.Source.IsRankOneModel A := by
  apply ChapterF.Source.IsRankOneModel.linear 2 (by decide)
  refine ⟨Representation.SL2FourNatural.F,inferInstance,inferInstance,?_,?_⟩
  · rw [Nat.card_eq_fintype_card,Representation.SL2FourNatural.card_field]
    norm_num
  · exact ⟨e.trans (Representation.SL2FourNatural.alternatingFiveEquiv.symm.trans
      (Theory.PSL2.sl2QuotientEquiv Representation.SL2FourNatural.F))⟩

variable {G : Type*} [Group G] [Finite G]

/-- The normalized original A₅ component gives the marked rank-one pair,
including its literal opposite S₃ quotient and both Borel identities. -/
theorem source_single_a5_rankOne_amalgam
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) (hout : ¬K ≤ M) :
    let Y := sourceResidual M Mc
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
    ChapterF.Source.HypothesisF11 ![K,Y ⊔ S₂] (T : Subgroup G) ∧
      Y = ⁅Y,S₂⁆ ∧ ChapterF.Source.borel K (T : Subgroup G) = M ⊓ K ∧
      ChapterF.Source.borel (Y ⊔ S₂) (T : Subgroup G) = S₂ ∧
      Nonempty (((Y ⊔ S₂ : Subgroup G) ⧸ pCore 2 (Y ⊔ S₂ : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)) := by
  let H := K ⊔ (T : Subgroup G)
  have hKH : K ≤ H := le_sup_left
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hH := source_single_a5_join_mem_HStar hG T hempty hM hu hmany hcard e hnot
    K hK hn eK hout
  let R := K.subgroupOf H
  let a : R ≃* K := subgroupOfEquivOfLe hKH
  let : R.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr
    (sup_le K.le_normalizer hn)
  have hRK : R.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  have hres : pResidual 2 H = R := by
    apply map_injective H.subtype_injective
    rw [hRK]
    exact single_component_join_residual T K hK hn
  have hgen : R ⊔ (T.subtype hTH : Subgroup H) = ⊤ := by
    rw [←hres]
    exact pResidual_sup_sylow_eq_top (T.subtype hTH)
  let q := a.toMonoidHom.pCoreQuotientEquiv (p := 2) a.surjective
    (IsPGroup.ker_isPGroup_of_injective a.injective)
  have hq : ChapterF.Source.IsRankOneModel (R ⧸ pCore 2 R) := five_rankOne (q.trans eK)
  have hh := source_normal_bender_hypothesis_F_1_1 hG T hempty hM hu hmany hcard e
    H hH R hgen hres hq
  dsimp only at hh ⊢
  rw [hRK] at hh
  have hS : (T : Subgroup G) ⊓ normalizer (K : Set G) = T := inf_eq_left.mpr hn
  rw [hS] at hh
  have hnR := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e
    H hH R hgen hres hq
  obtain ⟨_,_,hRT,_⟩ := source_normal_amalgam_core hG T hempty hM hu hmany hcard e
    H hH R hgen
  dsimp only at hnR hRT
  rw [hRK] at hnR hRT
  have hJ := (source_residual_actor_movement hG T hempty hM hu hmany hcard e
    _ (hRT.trans inf_le_left) le_sup_left hnR).2
  exact ⟨hh.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hJ⟩

open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Module
section Source
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hdegrees : ¬ (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1) →
      finrank (ZMod 2) (Additive F.Uhat) = 4 ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3))

include hG hempty hM hu hmany hcard e F hne g hgP hgH hK e5 hdegrees in
/-- Apply the rank-one entry to the same terminal component, discharging its
kernel and intrinsic quotient from the source numerical alternatives. -/
theorem source_terminal_single_a5_rankOne_amalgam_of_large_actor_degrees
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (hspan : K = conjugateSpanBy K (T : Subgroup G)) :
    let Y := sourceResidual M Mc
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
    ChapterF.Source.HypothesisF11 ![K,Y ⊔ S₂] (T : Subgroup G) ∧
      Y = ⁅Y,S₂⁆ ∧ ChapterF.Source.borel K (T : Subgroup G) = M ⊓ K ∧
      ChapterF.Source.borel (Y ⊔ S₂) (T : Subgroup G) = S₂ ∧
      Nonempty (((Y ⊔ S₂ : Subgroup G) ⧸ pCore 2 (Y ⊔ S₂ : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)) := by
  obtain ⟨⟨eK⟩,_⟩ := source_terminal_single_a5_parabolic_of_large_actor_degrees
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hK e5 hdegrees hnot hspan
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    rw [hspan]
    exact le_normalizer_conjugateSpanBy K (T : Subgroup G)
  exact source_single_a5_rankOne_amalgam hG T hempty hM hu hmany hcard e hnot K
    hK.local_component hn eK (hK.not_le hM.1.2 e)
end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
