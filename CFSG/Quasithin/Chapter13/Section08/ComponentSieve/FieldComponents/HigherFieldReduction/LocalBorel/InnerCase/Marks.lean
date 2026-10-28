module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase.Quotient

/-!
# The two source marks in the inner-actor argument

L₁ is literally O²(N_LT(V₁)); in the covered case the chosen X is literally
O²([L₁,T∩L]). Their definitions prove two-perfectness and normalization by
L₁T. Normalization of the constructed Borel, and the intrinsic identification
of its two-core with T*∩K*, make X* normalize the required Sylow.

The final theorem applies the normality-lifting and inverter construction
to exactly these marks. The quotient models distinguish A₆ from its actual
perfect central triple cover. The earlier marked order is about X/O₂(X),
not X*: their identification is justified only after normality is proved.

Source: Aschbacher–Smith, Notation 13.2.1, printed p.877, and the proof of
13.8.20, printed p.954/PDF p.971. The local Borel normalization and original
t's inversion are the preceding local inputs; no external-X conclusion is
an assumption.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase
open Components.Fitting TorusModels.Assembly
variable {G : Type*} [Group G] [Finite G]

/-- The actual source definitions supply containment, two-perfectness and normalization. -/
theorem marked_inputs (L L₁ T V₁ X : Subgroup G)
    (hdef : L₁ = (pResidual 2 (markedParabolic L T V₁)).map
      (markedParabolic L T V₁).subtype)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hmark : X = L₁ ∨ X = markedPlus L L₁ T) :
    X ≤ L₁ ∧ IsPPerfect 2 X ∧ L₁ ⊔ T ≤ normalizer (X : Set G) := by
  have hTM : T ≤ markedParabolic L T V₁ := le_inf le_sup_right hTV
  obtain ⟨hperfect, hnorm⟩ := marked_residual_inputs _ L₁ T hdef hTM
  rcases hmark with hm | hm
  · subst X
    exact ⟨le_rfl, hperfect, sup_le L₁.le_normalizer hnorm⟩
  · subst X
    have hn : normalizer ((⁅L₁, T ⊓ L⁆ : Subgroup G) : Set G) ≤
        normalizer (markedPlus L L₁ T : Set G) :=
      normalizer_le_normalizer_characteristic_image _ (pResidual 2 _)
    refine ⟨(map_subtype_le _).trans (le_normalizer_iff_commutator_le_left.mp
      (inf_le_left.trans hnorm)), isPPerfect_embedded_pResidual 2 _, sup_le ?_ ?_⟩
    · exact (normalizer_commutator_ge_left _ _).trans hn
    · apply le_trans ?_ hn
      intro t ht
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hnorm ht),
        mem_normalizer_iff_map_conj_eq.mp
          (((le_inf T.le_normalizer hTL).trans inf_normalizer_le_normalizer_inf) ht)]

/-- Borel normalization passes to its full Sylow two-core in H*. -/
theorem sylow_normalization_of_borel_core (H K L₁ T X : Subgroup G)
    [(Source.starImage H K).Normal] (hKH : K ≤ H)
    (hT : Chapter1.IsSylowIn 2 T H) (hX : X ≤ L₁)
    (hn : L₁ ⊔ T ≤ normalizer (borel H K T hKH hT : Set G))
    (hcore : (residualAt (sourceSylow H K T hT)).pCoreIn 2 = sourceSylow H K T hT) :
    Source.starImage H X ≤ normalizer
      ((Source.starImage H T ⊓ Source.starImage H K : Subgroup (Source.Hstar H)) : Set _) := by
  let B := borel H K T hKH hT
  have hBH : B ≤ H := (borel_le_component H K T hKH hT).trans hKH
  have hXB : X ≤ normalizer (B : Set G) := (hX.trans le_sup_left).trans hn
  have hstar : Source.starImage H X ≤ normalizer (Source.starImage H B : Set _) := by
    apply le_normalizer_iff.mpr
    rintro a ⟨aH, ha, rfl⟩ b ⟨bH, hb, rfl⟩
    exact ⟨aH * bH * aH⁻¹, le_normalizer_iff.mp hXB aH.val ha bH.val hb,
      by simp only [map_mul, map_inv]⟩
  have he : (Source.starImage H B).pCoreIn 2 =
      Source.starImage H T ⊓ Source.starImage H K := by
    rw [borel_star_intrinsic, ← map_pCoreIn_of_injective 2 _
      (Source.starImage H K).subtype (Source.starImage H K).subtype_injective,
      hcore, sourceSylow_image]
  rw [← he]
  exact hstar.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- Apply the inner-actor argument to the ordinary or covered source mark. -/
theorem external_of_marked_borel_core (H K L L₁ T V₁ X : Subgroup G)
    (hKH : K ≤ H) (hLH : L₁ ≤ H) (hgen : H = K ⊔ (L₁ ⊔ T))
    (hT : Chapter1.IsSylowIn 2 T H) [(K.subgroupOf H).Normal]
    [(Source.starImage H K).Normal]
    (hdef : L₁ = (pResidual 2 (markedParabolic L T V₁)).map
      (markedParabolic L T V₁).subtype)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hmark : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = L₁) ∨
      (IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = markedPlus L L₁ T))
    (hcard : Nat.card (X ⧸ pCore 2 X) = 3)
    (hB : L₁ ⊔ T ≤ normalizer (borel H K T hKH hT : Set G))
    (hcore : (residualAt (sourceSylow H K T hT)).pCoreIn 2 = sourceSylow H K T hT)
    (t : H) (ht : t.val ∈ T ⊓ L)
    (hinv : ∀ x ∈ X, t.val * x * t.val⁻¹ * x ∈ X.pCoreIn 2)
    (hi : markedActor H K T t ht.1 ∈ MulAut.innerSubgroup (Source.starImage H K)) :
    ExternalXAlternative H K X := by
  obtain ⟨hX, hp, hn⟩ := marked_inputs L L₁ T V₁ X hdef hTL hTV
    (hmark.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
  exact external_of_normalizes_sylow H K L₁ T X hKH hLH hX hgen hT
    inferInstance hp hn hcard (sylow_normalization_of_borel_core H K L₁ T X hKH hT hX hB hcore)
    t ht.1 hinv hi

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase
