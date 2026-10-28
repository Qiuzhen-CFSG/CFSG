module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.SourceAction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PrimeOrderLift


/-!
# The ordinary source node: residual, invariance, and index

Notation 13.2.1 defines L₁ as the embedded two-residual of N_LT(V₁).
This gives two-perfectness and T-normalization. In H/O₂(H), adjoining
T* ∩ K* leaves that residual unchanged. Relative component normality
makes the resulting node subgroup T*-invariant.

The index calculation uses the concrete cubic two-core quotient of L₁.
Its order bounds the odd index by three, and a cubic element survives
the actual two-group kernel, excluding index one. The argument adapts
the checked index calculation in Chapter 15's ParabolicIdentification.Local.
The cubic quotient is an explicit remaining model premise here, not a
claim that the ordinary source model has already been identified.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, printed p.877, and 13.8.25, printed p.959 (PDF p.976).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- The actual subgroup L₁* (T* ∩ K*), expressed as a join. -/
noncomputable def sourceNode (H K L₁ T : Subgroup G) : Subgroup (Source.Hstar H) :=
  Source.starImage H L₁ ⊔ (Source.starImage H T ⊓ Source.starImage H K)

private theorem normalized_sup_index (Y S : Subgroup G)
    (hn : S ≤ normalizer (Y : Set G)) : S.relIndex (Y ⊔ S) = S.relIndex Y := by
  let J := Y ⊔ S
  let _ : (Y.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hn)
  have aux (A B : Subgroup J) [A.Normal] : B.relIndex (A ⊔ B) = B.relIndex A := by
    have hm : A.relIndex B * B.relIndex (A ⊔ B) = A.relIndex B * B.relIndex A := by
      calc
        _ = (B ⊓ A).relIndex (A ⊔ B) := by
          rw [← inf_relIndex_left (H := B) (K := A)]
          exact relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
        _ = (B ⊓ A).relIndex A * A.relIndex (A ⊔ B) :=
          (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
        _ = _ := by simp [inf_relIndex_right, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (index_ne_zero_of_finite : A.relIndex B ≠ 0)) hm
  have hi := aux (Y.subgroupOf J) (S.subgroupOf J)
  rw [← subgroupOf_sup le_sup_left le_sup_right,
    relIndex_subgroupOf le_rfl, relIndex_subgroupOf le_sup_left] at hi
  exact hi

omit [Finite G] in
/-- Normalization transports through the literal star quotient. -/
theorem star_normalizes (H A B : Subgroup G)
    (hn : A ≤ normalizer (B : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H B : Set (Source.Hstar H)) :=
  (map_mono ((comap_mono hn).trans (B.le_normalizer_comap H.subtype))).trans
    ((B.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))

/-- Two-perfectness and normalization follow from the source definition. -/
theorem notation_residual_inputs (L L₁ T V₁ : Subgroup G)
    (hdef : L₁ = (pResidual 2 ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
      ((L ⊔ T) ⊓ normalizer (V₁ : Set G)).subtype)
    (hTV : T ≤ normalizer (V₁ : Set G)) :
    IsPPerfect 2 L₁ ∧ T ≤ normalizer (L₁ : Set G) := by
  subst L₁
  refine ⟨isPPerfect_embedded_pResidual 2 _, (show T ≤ (L ⊔ T) ⊓ normalizer (V₁ : Set G) from le_inf le_sup_right hTV).trans ?_⟩
  have hn := (pResidual 2 ((L ⊔ T) ⊓ normalizer (V₁ : Set G) : Subgroup G)).le_normalizer_map
    ((L ⊔ T) ⊓ normalizer (V₁ : Set G)).subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn

omit [Finite G] in
/-- Component containment uses the earlier L₁ ≤ K conclusion. -/
theorem sourceNode_le_component (H K L₁ T : Subgroup G) (hLK : L₁ ≤ K) :
    sourceNode H K L₁ T ≤ Source.starImage H K :=
  sup_le (map_mono (comap_mono hLK)) inf_le_right

omit [Finite G] in
/-- The actual node is normalized by T*, using only relative normality. -/
theorem sourceNode_normalized (H K L₁ T : Subgroup G)
    (hTH : T ≤ H) (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal)
    (hn : T ≤ normalizer (L₁ : Set G)) :
    Source.starImage H T ≤ normalizer (sourceNode H K L₁ T : Set (Source.Hstar H)) := by
  have hTK : T ≤ normalizer (K : Set G) :=
    hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKn)
  have hTI := (le_inf (Source.starImage H T).le_normalizer (star_normalizes H T K hTK)).trans
    inf_normalizer_le_normalizer_inf
  exact (le_inf (star_normalizes H T L₁ hn) hTI).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit [Finite G] in
/-- The marked residual identity survives passage through the actual kernel. -/
theorem sourceNode_residual (H K L₁ T : Subgroup G) (hLH : L₁ ≤ H)
    (hp : IsPPerfect 2 L₁) (hT : IsPGroup 2 T)
    (hn : T ≤ normalizer (L₁ : Set G)) :
    (pResidual 2 (sourceNode H K L₁ T)).map (sourceNode H K L₁ T).subtype =
      Source.starImage H L₁ := by
  have hp' : IsPPerfect 2 (Source.starImage H L₁) :=
    (hp.of_surjective (subgroupOfEquivOfLe hLH).symm.toMonoidHom
      (subgroupOfEquivOfLe hLH).symm.surjective).of_surjective
        ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (L₁.subgroupOf H))
        ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)
  exact embedded_pResidual_join_pGroup _ _ hp'
    ((hT.comap_subtype.map _).to_le inf_le_left)
    (inf_le_left.trans (star_normalizes H T L₁ hn))

private theorem star_cubic (H Y : Subgroup G) (hYH : Y ≤ H)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    ∃ y : Source.starImage H Y, orderOf y = 3 := by
  have hd : 3 ∣ Nat.card Y := hY ▸ (pCore 2 Y).index_dvd_card
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 hd
  let f : Y →* Source.Hstar H := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hYH)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hYH)).ker)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hYH)
  have ho : orderOf (f y) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk y
      (hy ▸ (by decide : Nat.Coprime 2 3))).trans hy
  have hm : f y ∈ Source.starImage H Y := ⟨⟨y, hYH y.property⟩, y.property, rfl⟩
  exact ⟨⟨f y, hm⟩, (Subgroup.orderOf_coe _).symm.trans ho⟩

/-- A cubic intrinsic quotient gives index three over the actual component Sylow. -/
theorem sourceNode_index_three_of_cubic (H K L₁ T : Subgroup G)
    (hKH : K ≤ H) (hLK : L₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hT : IsSylowIn 2 T H) (hn : T ≤ normalizer (L₁ : Set G))
    (hcard : Nat.card (L₁ ⧸ pCore 2 L₁) = 3) :
    IsSylowIn 2 (Source.starImage H T ⊓ Source.starImage H K) (Source.starImage H K) ∧
      (Source.starImage H T ⊓ Source.starImage H K).relIndex (sourceNode H K L₁ T) = 3 := by
  have hs := (Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.component_inter_sylow H T K hT hKH hK).2
  have hinf : Source.starImage H (T ⊓ K) = Source.starImage H T ⊓ Source.starImage H K :=
    Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.starImage_inter_sylow H T K hT
  change IsSylowIn 2 (Source.starImage H (T ⊓ K)) (Source.starImage H K) at hs
  rw [hinf] at hs
  refine ⟨hs, ?_⟩
  let S := Source.starImage H T ⊓ Source.starImage H K
  let D := Source.starImage H L₁
  let P := sourceNode H K L₁ T
  have hsP := hs.restrict (show S ≤ P from le_sup_right)
    (sourceNode_le_component H K L₁ T hLK)
  have hi : S.relIndex P = S.relIndex D :=
    normalized_sup_index D S (inf_le_left.trans (star_normalizes H T L₁ hn))
  have hdiv : S.relIndex P ∣ Nat.card L₁ := by
    rw [hi]
    exact (relIndex_dvd_card S D).trans
      (((L₁.subgroupOf H).card_map_dvd (QuotientGroup.mk' (pCore 2 H))).trans
        ((Nat.card_congr (subgroupOfEquivOfLe (hLK.trans hKH)).toEquiv).dvd))
  have hsize : Nat.card (pCore 2 L₁) * 3 = Nat.card L₁ := by
    simpa only [Subgroup.index, hcard] using (pCore 2 L₁).card_mul_index
  obtain ⟨n, hn'⟩ := (pCore_isPGroup (p := 2) (G := L₁)).exists_card_eq
  rw [← hsize, hn'] at hdiv
  have hodd : ¬ 2 ∣ S.relIndex P := by
    obtain ⟨Q, hQ⟩ := hsP
    have he : S.subgroupOf P = (Q : Subgroup P) := by
      change (Q : Subgroup P).map P.subtype = S at hQ
      rw [← hQ]
      exact comap_map_eq_self_of_injective P.subtype_injective _
    change ¬ 2 ∣ (S.subgroupOf P).index
    rw [he]
    exact Q.not_dvd_index
  have hc : (S.relIndex P).Coprime 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hodd).symm
  have hd3 : S.relIndex P ∣ 3 := (hc.pow_right n).dvd_of_dvd_mul_left hdiv
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd3 with hone | hthree
  · have hDS : D ≤ S := (show D ≤ P from le_sup_left).trans (relIndex_eq_one.mp hone)
    obtain ⟨y, hy⟩ := star_cubic H L₁ (hLK.trans hKH) hcard
    let x : S := ⟨y, hDS y.property⟩
    have hx : orderOf x = 3 := by
      rw [← Subgroup.orderOf_coe x, show (x : Source.Hstar H) = y from rfl,
        Subgroup.orderOf_coe y, hy]
    have hc := (isSylowIn_iff.mp hsP).1.orderOf_coprime (by decide : Nat.Coprime 2 3) x
    rw [hx] at hc
    exact (by decide : ¬ Nat.Coprime 3 3) hc |>.elim
  · exact hthree
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource

end
