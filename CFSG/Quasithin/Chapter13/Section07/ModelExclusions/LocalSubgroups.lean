module

public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.CoveredSeed
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# Lifting the two invariant cubic directions to the source subgroups

The two-core of L₁ lies in the prescribed Sylow subgroup T. Consequently
T-normalized two-perfect subgroups of L₁ are determined by their images
modulo that core. The marked order-nine quotient has just the two
T-invariant cubic directions L₀ and L₁,+. Lifting the exact marked maps
gives the corresponding classification of proper nontrivial source
subgroups, used in the proof of 13.7.5(7).

Source: Aschbacher–Smith, 13.2.2(3) and 13.7.5(7), printed pp.877,938.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalAction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

private theorem point_core_le_sylow : (sourceOne L T V₁).pCoreIn 2 ≤ (T : Subgroup G) := by
  apply (isPGroup_pCoreIn 2 _).le_sylow_of_normalized T
  exact (T_normalizes_one L T V₁ d.line_stable).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- Recover containment of a two-perfect source subgroup from its exact core image. -/
theorem le_of_point_residual_image_le {A B : Subgroup G}
    (hA : A ≤ sourceOne L T V₁) (hpA : IsPPerfect 2 A)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (him : Section08.Source.starImage (sourceOne L T V₁) A ≤
      Section08.Source.starImage (sourceOne L T V₁) B) : A ≤ B := by
  apply le_of_isPPerfect_of_le_sup_of_normalizes A B (T : Subgroup G) hpA T.isPGroup' hTB
  intro x hx
  let a : sourceOne L T V₁ := ⟨x, hA hx⟩
  have hm := him (mem_map_of_mem (QuotientGroup.mk' (pCore 2 (sourceOne L T V₁)))
    (show a ∈ A.subgroupOf (sourceOne L T V₁) from hx))
  obtain ⟨b, hb, hba⟩ := hm
  have hn : b⁻¹ * a ∈ pCore 2 (sourceOne L T V₁) := QuotientGroup.eq.mp hba
  have hnt : ((b⁻¹ * a : sourceOne L T V₁) : G) ∈ (T : Subgroup G) :=
    point_core_le_sylow d (mem_map_of_mem (sourceOne L T V₁).subtype hn)
  have he : x = b.val * ((b⁻¹ * a : sourceOne L T V₁) : G) := by
    change a.val = b.val * (b.val⁻¹ * a.val)
    group
  rw [he]
  exact (B ⊔ (T : Subgroup G)).mul_mem (mem_sup_left hb) (mem_sup_right hnt)

/-- T-normalized two-perfect subgroups of L₁ retain their full subgroup identity modulo O₂(L₁). -/
theorem eq_of_point_residual_image_eq {A B : Subgroup G}
    (hA : A ≤ sourceOne L T V₁) (hB : B ≤ sourceOne L T V₁)
    (hpA : IsPPerfect 2 A) (hpB : IsPPerfect 2 B)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (him : Section08.Source.starImage (sourceOne L T V₁) A =
      Section08.Source.starImage (sourceOne L T V₁) B) : A = B :=
  le_antisymm (le_of_point_residual_image_le d hA hpA hTB him.le)
    (le_of_point_residual_image_le d hB hpB hTA him.symm.le)

omit d [Finite G] in
private theorem point_full_image :
    Section08.Source.starImage (sourceOne L T V₁) (sourceOne L T V₁) = ⊤ := by
  rw [Section08.Source.starImage, subgroupOf_self,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

/-- The four possibilities are actual subgroups of the original ambient group. -/
theorem covered_point_subgroup_alternatives
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    {Y : Subgroup G} (hY : Y ≤ sourceOne L T V₁) (hpY : IsPPerfect 2 Y)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    Y = ⊥ ∨ Y = zero L ∨ Y = plus L T V₁ ∨ Y = sourceOne L T V₁ := by
  rcases NaturalModels.quotient_alternatives d with ⟨e, _⟩ | ⟨e, he⟩
  · obtain ⟨ec⟩ := hcover
    have hc := Nat.card_congr (centerCongr (e.symm.trans ec)).toEquiv
    rw [alternatingGroup.center_eq_bot (by simp), card_bot,
      Representation.Hexacode.even_center_card] at hc
    omega
  · obtain ⟨a⟩ := NaturalModels.covered_natural d e he
    have hf := Section08.SourceCompletion.CoverFactorization.source_factorization a
    let C := Section08.Source.starImage (sourceOne L T V₁) Y
    have hcard : Nat.card C ∣ 3 ^ 2 := by
      have hc := C.card_subgroup_dvd_card
      rw [a.one_quotient_card hf] at hc
      exact hc
    obtain ⟨k, hk, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hcard
    interval_cases k
    · left
      have hCb : C = ⊥ := eq_bot_of_card_eq C (by simpa using hc)
      apply bot_unique
      apply le_of_point_residual_image_le d hY hpY
        (show (T : Subgroup G) ≤ normalizer ((⊥ : Subgroup G) : Set G) by
          rw [Subgroup.normalizer_eq_top]; exact le_top)
      change C ≤ _
      rw [hCb]
      exact bot_le
    · have hstable : ∀ t : (T : Subgroup G), ∀ x ∈ C,
          coreAction (one L T V₁)
            ⟨t.val, T_normalizes_one L T V₁ d.line_stable t.property⟩ x ∈ C := by
        intro t x hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [coreAction_mk]
        exact mem_map_of_mem (QuotientGroup.mk' (pCore 2 (one L T V₁)))
          ((mem_normalizer_iff.mp (hTY t.property) y.val).mp hy)
      rcases a.invariant_marked_line hf C (by simpa using hc) hstable with hz | hx
      · right; left
        rw [zeroCoreMap, localCoreMap_range] at hz
        exact eq_of_point_residual_image_eq d hY
          (zero_le_one_of_factorization L T V₁ hf) hpY
          (residual_isPPerfect (centralPreimage L)) hTY
          (d.normalizes_L.trans (normalizer_le_zero_normalizer L)) hz
      · right; right; left
        rw [plusCoreMap, localCoreMap_range] at hx
        exact eq_of_point_residual_image_eq d hY (plus_le_one L T V₁ d.line_stable)
          hpY (residual_isPPerfect _) hTY
          (T_normalizes_plus L T V₁ d.normalizes_L d.line_stable) hx
    · right; right; right
      have hCt : C = ⊤ := eq_of_le_of_card_ge le_top (by
        rw [card_top, a.one_quotient_card hf]
        exact hc.ge)
      apply eq_of_point_residual_image_eq d hY le_rfl hpY
        (residual_isPPerfect (parabolic L T V₁)) hTY (T_normalizes_one L T V₁ d.line_stable)
      exact hCt.trans (point_full_image (L := L) (T := T) (V₁ := V₁)).symm

/-- The exact proper nontrivial alternatives quoted in13.7.5(7). -/
theorem covered_proper_point_subgroup
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    {Y : Subgroup G} (hY : Y < sourceOne L T V₁) (hne : Y ≠ ⊥)
    (hpY : IsPPerfect 2 Y) (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    Y = zero L ∨ Y = plus L T V₁ := by
  rcases covered_point_subgroup_alternatives d hcover hY.le hpY hTY with h | h | h | h
  · exact (hne h).elim
  · exact Or.inl h
  · exact Or.inr h
  · exact (hY.ne h).elim

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
