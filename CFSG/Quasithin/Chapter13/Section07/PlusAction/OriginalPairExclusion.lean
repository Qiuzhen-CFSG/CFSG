module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalThompsonModels
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Quotient
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryParabolic
/-!
# Excluding the paired Thompson section

The literal Thompson subgroup is normal in K(L₁T). If its quotient modulo
its own two-core were S₃ × S₃, then the two-perfect point residual L₁
would lie inside that Thompson subgroup by ambient three-rank two. Since
that subgroup lies in KR₁, absorbing the two-group R₁ forces L₁ ≤ K,
contrary to the chosen primitive witness.

Source: Aschbacher--Smith 13.7.4(1), printed p.937.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionQuotients.FiveSeed.BarMarking
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
theorem source_primitive_thompson_not_pair
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (J : Subgroup H)
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hnot : ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤ J.map H.subtype) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    let X := J.map H.subtype ⊔ R
    let W := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map (QuotientGroup.mk' (pCore 2 X))
    ¬ Nonempty (W ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let P := F.L₁ ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  let X := K ⊔ R
  let W := elementaryAbelianMaxJ (⊤ : Subgroup X)
  let N := W.map X.subtype
  let Y := K ⊔ P
  let B := F.L₁.subgroupOf Y
  let NY := N.subgroupOf Y
  have hKH : K ≤ H := map_subtype_le J
  have hYH : Y ≤ H := sup_le hKH h.local_le
  have hXY : X ≤ Y := sup_le le_sup_left ((pCoreIn_le 2 P).trans le_sup_right)
  have hPY : P ≤ Y := le_sup_right
  have hBY : F.L₁ ≤ Y := le_sup_left.trans hPY
  have hNX : N ≤ X := map_subtype_le W
  have hNY : N ≤ Y := hNX.trans hXY
  have hPR : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hPX : P ≤ normalizer (X : Set G) :=
    (le_inf (h.local_le.trans hJn) hPR).trans
      (normalizer_inf_normalizer_le_normalizer_sup K R)
  have hYX : Y ≤ normalizer (X : Set G) := sup_le
    ((show K ≤ X from le_sup_left).trans X.le_normalizer) hPX
  let : W.Characteristic := elementaryAbelianMaxJ_top_characteristic
  have hYN : Y ≤ normalizer (N : Set G) :=
    hYX.trans (normalizer_le_normalizer_characteristic_image X W)
  let : NY.Normal := normal_subgroupOf_of_le_normalizer hYN
  let : W.Normal := inferInstance
  let eW := (Normal.isSubnormal (inferInstance : W.Normal)).quotientCoreImageEquiv 2
  let eNW : NY ≃* W := (subgroupOfEquivOfLe hNY).trans
    (W.equivMapOfInjective X.subtype X.subtype_injective).symm
  dsimp only
  rintro ⟨epair⟩
  let eN : (NY ⧸ pCore 2 NY) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
    (QuotientGroup.congr _ _ eNW (pCore_map_iso 2 eNW)).trans (eW.trans epair)
  have hp : IsPPerfect 2 F.L₁ := isPPerfect_embedded_pResidual 2 _
  have hpB : IsPPerfect 2 B := hp.of_surjective
    (subgroupOfEquivOfLe hBY).symm.toMonoidHom (subgroupOfEquivOfLe hBY).symm.surjective
  have hr : primeRank 3 Y ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hYH) (inclusion_injective hYH)).trans
      (source_H_stronglyQuasithin d h 3 Nat.prime_three (by decide))
  have hres : F.L₁ = sourceOne L T V₁ := by
    have hh := normalizer_residual_eq L V₁ (T : Subgroup G) T.isPGroup' d.normalizes_L
    change sourceOne L T V₁ =
      (pResidual 2 (L ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
        (L ⊓ normalizer (V₁ : Set G)).subtype at hh
    have hn : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) := h.normalizer_point_eq
    rw [hn] at hh
    exact hh.symm
  have hc : Nat.card (F.L₁ ⧸ pCore 2 F.L₁) = 3 := by
    rw [hres]
    exact Section03.Noncentrality.ordinary_point_residual_quotient_card d eL
  have ho : ∃ m n : ℕ, Nat.card B ∣ 2 ^ m * 3 ^ n := by
    obtain ⟨m,hm⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := F.L₁))
    refine ⟨m,1,?_⟩
    have hcardB : Nat.card B = Nat.card F.L₁ :=
      Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv
    rw [hcardB, card_eq_card_quotient_mul_card_subgroup (pCore 2 F.L₁),
      hc, hm, pow_one, Nat.mul_comm]
  have hb := NormalSymmetricThreePairRank.le_normal_of_quotient_pair NY eN B hpB hr ho
  have hL1X : F.L₁ ≤ X := by
    intro x hx
    exact hNX (hb (show (⟨x,hBY hx⟩ : Y) ∈ B from hx))
  exact hnot (le_of_isPPerfect_of_le_sup_of_normalizes F.L₁ K R hp
    (isPGroup_pCoreIn 2 P) (((pCoreIn_le 2 P).trans h.local_le).trans hJn) hL1X)
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
