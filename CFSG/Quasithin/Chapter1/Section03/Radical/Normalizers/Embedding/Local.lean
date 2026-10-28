module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Basic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import Theory.Quasithin.Rank

/-!
# Embedding the residual in a characteristic-subgroup normalizer

For C characteristic inside R = O₂(Ξ_p(L)T), the subgroup N = N_G(C)
contains T and Y = N_L(R)^∞. It is a proper two-local in the simple QTKE
ambient group. Thus N/O₂(N) is SQTK, and the actual local-family witness
for Y transports to N with T still Sylow. Applying the universal A.3.12
and A.3.8 inputs constructs the unique containing C-component K, normal
in N. The commutator identity [N_L(C)^∞,Y] = N_L(C)^∞ then puts N_L(C)^∞
inside K.

This is the first embedding step in the proof of Proposition 1.3.8,
Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.513.
The residual C-component witness is an explicit input from the preceding
Frattini argument. No elimination of the A.3.12 alternatives is asserted here.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- N_G(C) is an actual two-local; C is characteristic in R, not in G. -/
theorem characteristic_normalizer_isTwoLocal (p : ℕ) (L T : Subgroup G)
    (C : Subgroup (radicalCore p L T)) (hC : C ≠ ⊥) :
    IsTwoLocal (normalizer (C.map (radicalCore p L T).subtype : Set G)) := by
  refine ⟨C.map (radicalCore p L T).subtype, ?_, ?_, rfl⟩
  · exact fun he => hC ((C.map_eq_bot_iff_of_injective
      (radicalCore p L T).subtype_injective).mp he)
  · exact ((radicalCore_isTwoGroup p L T).to_subgroup C).map _

/-- The odd-rank and K-group premises required in the A.3 quotient are derived
from the genuine ambient hypothesis. -/
theorem characteristic_normalizer_quotient_sqtk {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G) (p : ℕ) (L T : Subgroup G)
    (C : Subgroup (radicalCore p L T)) (hC : C ≠ ⊥) :
    IsSQTK 𝒦 (XiQuotient
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) := by
  have hN := hG.twoLocal_sqtk (characteristic_normalizer_isTwoLocal p L T C hC)
  refine ⟨?_, hN.isKGroup.quotient _⟩
  intro q hq ho
  let : Fact q.Prime := ⟨hq⟩
  exact (primeRank_quotient_le_of_isTwoGroup q ho _ pCore_isPGroup).trans
    (hN.stronglyQuasithin q hq ho)

/-- Construction of K ∈ C(N), retaining the actual images in N/O₂(N).
Normality is relative to N and hence also gives T-invariance. -/
theorem exists_normal_component
    {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ (S : Sylow 2 A) (B : Subgroup A),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (hA38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK 𝒦 A → pCore 2 A = ⊥ → ∀ K : Subgroup A, K.IsCComponent →
      K.Normal ∨ (normalizer (K : Set A)).index = 2 ∧ NonnormalCComponentModel K)
    (p : ℕ) (L : Subgroup G) (T : Sylow 2 G)
    (hL : L ∈ Chapter1.L G T) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hY : ((normalizerResidual L (radicalCore p L T)).subgroupOf
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G))).IsCComponent)
    (C : Subgroup (radicalCore p L T)) [C.Characteristic] (hC : C ≠ ⊥) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let Y := normalizerResidual L (radicalCore p L T)
    ∃ K : Subgroup G, K ∈ cComponentsIn N ∧ Y ≤ K ∧
      (∀ D : Subgroup G, D ∈ cComponentsIn N → Y ≤ D → D = K) ∧
      (K.subgroupOf N).Normal ∧ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      A312Embedding ((Y.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))
        ((K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) := by
  let R := radicalCore p L T
  let N := normalizer (C.map R.subtype : Set G)
  let Y := normalizerResidual L R
  have hRN : normalizer (R : Set G) ≤ N :=
    normalizer_le_normalizer_characteristic_image R C
  have hTN : (T : Subgroup G) ≤ N := (t_le_normalizer_radicalCore p L T).trans hRN
  have hYN : Y ≤ N := (normalizerResidual_le_normalizer L R).trans hRN
  let S : Sylow 2 N := T.subtype hTN
  have hYL : Y.subgroupOf N ∈ Chapter1.L N S := by
    change Y.subgroupOf N ∈ Chapter1.L N ((T : Subgroup G).subgroupOf N)
    exact (mem_LIn_iff_subgroupOf hTN hYN).mp
      ⟨hYN, Y_mem_L_of_cComponent p hL hY⟩
  have hSY : (S : Subgroup N) ≤ normalizer (Y.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hYN]
    exact comap_mono (t_le_normalizer_Y p hTL)
  obtain ⟨K₀, hK₀, hYK₀, hu, he, hn⟩ :=
    lemma_1_2_4_of_A_3_12_A_3_8 hA312 hA38
      (characteristic_normalizer_quotient_sqtk hG p L T C hC) S hYL
  have hKm : (K₀.map N.subtype).subgroupOf N = K₀ :=
    comap_map_eq_self_of_injective N.subtype_injective _
  have hnormal : ((K₀.map N.subtype).subgroupOf N).Normal := hKm.symm ▸ hn hSY
  have hNK : N ≤ normalizer (K₀.map N.subtype : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le K₀)).mp hnormal
  refine ⟨K₀.map N.subtype, ⟨map_subtype_le _, hKm.symm ▸ hK₀⟩,
    ?_, ?_, hnormal, hTN.trans hNK, ?_⟩
  · simpa only [map_subgroupOf_eq_of_le hYN] using map_mono (f := N.subtype) hYK₀
  · intro D hD hYD
    have hd := congrArg (map N.subtype) (hu _ hD.2 (comap_mono hYD))
    change (D.subgroupOf N).map N.subtype = K₀.map N.subtype at hd
    exact (map_subgroupOf_eq_of_le hD.1).symm.trans hd
  · change A312Embedding ((Y.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))
      (((K₀.map N.subtype).subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))
    rw [hKm]
    exact he

omit [Finite G] in
/-- The source's [L_C,Y] = L_C puts L_C inside the relatively normal K. -/
theorem residual_le_component (L R K : Subgroup G) (C : Subgroup R)
    (hKN : K ≤ normalizer (C.map R.subtype : Set G))
    (hK : (K.subgroupOf (normalizer (C.map R.subtype : Set G))).Normal)
    (hYK : normalizerResidual L R ≤ K)
    (hcomm : ⁅normalizerResidual L (C.map R.subtype), normalizerResidual L R⁆ =
      normalizerResidual L (C.map R.subtype)) :
    normalizerResidual L (C.map R.subtype) ≤ K := by
  rw [← hcomm]
  apply (commutator_mono le_rfl hYK).trans
  apply le_normalizer_iff_commutator_le_right.mp
  exact (normalizerResidual_le_normalizer L _).trans
    ((normal_subgroupOf_iff_le_normalizer hKN).mp hK)

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding
