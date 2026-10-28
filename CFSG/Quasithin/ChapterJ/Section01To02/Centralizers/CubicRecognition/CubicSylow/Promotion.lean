module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.Basic
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Promotion of the cubic subgroup to an ambient Sylow

Once Z(R) has ambient image B, characteristicity forces N_G(R) into
N_G(B). The local Sylow index is then prime to three in N_G(R), and
the Sylow normalizer congruence makes the full index prime to three.
The resulting ambient Sylow has exactly the original image of R.

The hypothesis identifying the center is discharged by the nonabelian
branch of the cubic structure argument; it is not assumed in that argument.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448).
-/

public section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The characteristic center controls the literal ambient normalizer. -/
theorem normalizer_le_NB_of_center (R : Sylow 3 c.NB)
    (hcenter : (center (ambient c R)).map (ambient c R).subtype = c.B) :
    normalizer (ambient c R : Set G) ≤ c.NB := by
  change normalizer (ambient c R : Set G) ≤ normalizer (c.B : Set G)
  rw [← hcenter]
  exact normalizer_le_normalizer_characteristic_image (ambient c R) (center (ambient c R))

/-- No conjugation or enlargement changes R in the Sylow promotion. -/
theorem exists_ambient_sylow_of_center (R : Sylow 3 c.NB)
    (hcenter : (center (ambient c R)).map (ambient c R).subtype = c.B) :
    ∃ S : Sylow 3 G, (S : Subgroup G) = ambient c R := by
  have hnormalizer := normalizer_le_NB_of_center c R hcenter
  have hindex : (ambient c R).relIndex c.NB = (R : Subgroup c.NB).index := by
    simpa only [ambient, ← MonoidHom.range_eq_map, c.NB.range_subtype, relIndex_top_right] using
      relIndex_map_map_of_injective (R : Subgroup c.NB) ⊤ c.NB.subtype_injective
  have hdiv : (ambient c R).relIndex (normalizer (ambient c R : Set G)) ∣
      (ambient c R).relIndex c.NB :=
    dvd_of_mul_right_eq _ (relIndex_mul_relIndex (ambient c R)
      (normalizer (ambient c R : Set G)) c.NB le_normalizer hnormalizer)
  have hnot : ¬ 3 ∣ (ambient c R).relIndex (normalizer (ambient c R : Set G)) := by
    intro h
    exact R.not_dvd_index (hindex ▸ h.trans hdiv)
  obtain ⟨height, hcard⟩ := (ambient_isPGroup c R).exists_card_eq
  have hcongr := Sylow.card_quotient_normalizer_modEq_card_quotient hcard
  have hambient : ¬ 3 ∣ (ambient c R).index := by
    intro h
    apply hnot
    exact (hcongr.dvd_iff dvd_rfl).mpr h
  exact ⟨(ambient_isPGroup c R).toSylow hambient, rfl⟩

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow
