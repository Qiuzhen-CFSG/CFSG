module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Sporadic
public import Theory.Mathieu.M22.Properties.ComponentCentralizer

/-!
# Exclusion of the remaining marked M₂₂ component in 14.3.20

The actual component quotient embeds subnormally in C_G(d)/⟨d⟩ and contains
the same marked z. Quasithinness bounds this quotient's three-rank by two,
and its two-core is trivial. The intrinsic M₂₂ component-centralizer theorem
therefore bounds the marked centralizer by 768. The supplied quaternion
extension contains a subgroup of order 1152, giving the contradiction.

The original-hypothesis wrapper preserves every source parameter, including
terminal solvability, although the exclusion needs only quasithinness beyond
the published local contract. The final factor consumer discharges the M₂₂
premise; geometry, core construction, local extension and even-model exclusion
remain explicit. This module does not claim full original 14.3.20.

Source: Aschbacher--Smith, 14.3.20, final paragraph on printed p.998,
and the sporadic alternative 1.1.5(3)(f), printed p.502.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
variable {F : InvariantFlag T V 2} {L A : Subgroup G}

namespace MarkedPoint
variable (P : MarkedPoint F L A)

/-- The supplied local extension contains a subgroup of order 1152. -/
theorem quotientCentralizer_card_ge (z : P.globalCentralizer)
    (h : P.QuotientCentralizerStructure z) :
    1152 ≤ Nat.card (centralizer ({P.pointQuotientMap z} : Set P.PointQuotient)) := by
  obtain ⟨W, _, Q, hQ, ⟨d⟩, ⟨e⟩⟩ := h
  let := hQ
  have hq : Nat.card (W ⧸ Q) = 36 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  have hw : Nat.card W = 1152 := by
    have hc := Q.card_mul_index
    rw [d.card,index_eq_card,hq] at hc
    omega
  exact hw ▸ W.card_le_card_group

/-- The literal deleted-point quotient has trivial two-core. -/
theorem pointQuotient_twoCore_eq_bot
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element) :
    pCore 2 P.PointQuotient = ⊥ := by
  let e := QuotientGroup.quotientMulEquivOfEq (P.pointKernel_eq_core hcore)
  have he := pCore_map_iso 2 e
  rw [pCore_quotient_pCore_eq_bot] at he
  exact (map_eq_bot_iff_of_injective _ e.injective).mp he

/-- The original local extension excludes the actual marked M₂₂ component. -/
theorem not_mathieuTwentyTwoComponent
    (hG : IsQuasithin G) (hA : ElementaryFactor F L A)
    (z : G) (hz : F.Vi 1 = zpowers z)
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element)
    (hlocal : P.QuotientCentralizerStructure (P.markedGenerator hA.seed_le z hz)) :
    ¬ P.MathieuTwentyTwoComponent z := by
  intro h
  obtain ⟨t,j,hj,hsub,hmark,ht,_,_⟩ :=
    P.exists_marked_model_embedding hA ClassificationModels.SporadicName.m22 z hz hcore h
  have hC : Nat.card (centralizer ({j t} : Set P.PointQuotient)) ∣ 2304 := by
    rw [hmark]
    exact P.quotientCentralizer_card_dvd _ hlocal
  have hr : primeRank 3 P.PointQuotient ≤ 2 := by
    have hk : Nat.Coprime 3 (Nat.card P.pointQuotientMap.ker) := by
      rw [P.pointQuotientMap_ker,P.pointKernel_card]
      decide
    exact (primeRank_le_of_surjective_of_coprime 3 P.pointQuotientMap
      (QuotientGroup.mk'_surjective _) hk).trans
      ((isQuasithin_iff_twoLocal.mp hG P.globalCentralizer
        (isTwoLocal_involution_centralizer P.point_order)) 3 (by decide) (by decide))
  have hu : Nat.card (centralizer ({j t} : Set P.PointQuotient)) ≤ 768 :=
    _root_.Sporadic.Mathieu.m22_subnormal_marked_centralizer_card_le
    j hj hsub hr (P.pointQuotient_twoCore_eq_bot hcore) t ht hC
  rw [hmark] at hu
  have hl := P.quotientCentralizer_card_ge _ hlocal
  omega
end MarkedPoint

/-- Quasithinness discharges the published M₂₂ exclusion contract. -/
theorem mathieuTwentyTwoExclusionSource_of_quasithin (hG : IsQuasithin G)
    (F : InvariantFlag T V 2) (L : Subgroup G) :
    MathieuTwentyTwoExclusionSource F L := by
  intro A hA _ P z hz _ _ hcore hlocal h22
  exact P.not_mathieuTwentyTwoComponent hG hA z hz hcore hlocal h22

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

set_option linter.unusedVariables false in
/-- The M₂₂ source obligation under exactly the original factor hypotheses.
The unused arguments deliberately preserve the original consumer signature. -/
theorem source_mathieuTwentyTwoExclusion
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
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot) :
    MathieuTwentyTwoExclusionSource F (sourceResidual M Mc) :=
  mathieuTwentyTwoExclusionSource_of_quasithin hG.quasithin F (sourceResidual M Mc)

/-- Apply the completed sporadic exclusion to the original factor consumer. -/
theorem factorSelfCentralizing_of_local_sporadic_inputs
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
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hgeometry : FourCenterSource F (sourceResidual M Mc))
    (hcore : CoreComponentSource F (sourceResidual M Mc))
    (hlocal : QuotientCentralizerSource F (sourceResidual M Mc))
    (heven : EvenExclusionSource F (sourceResidual M Mc)) :
    FactorSelfCentralizing F (sourceResidual M Mc) :=
  factorSelfCentralizing_of_local_mathieuTwentyTwo_inputs
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hgeometry hcore hlocal heven
    (source_mathieuTwentyTwoExclusion hG T hempty hM hu hmany hcard e hnot F hne
      g hgP hgH hs)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
