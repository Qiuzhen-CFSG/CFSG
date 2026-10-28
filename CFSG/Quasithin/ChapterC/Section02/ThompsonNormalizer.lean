module
public import Theory.GroupTheory.ElementaryThompsonQuotientNormalizer
public import Theory.GroupTheory.QuotientIntersection

/-!
# The marked normalizer restriction for pushing up

Characteristic-normalizer control for a nontrivial two-subgroup R controls
the normalizer of its actual Thompson image in every quotient whose kernel
lies in R. Intersecting with the component image gives the original marked
intersection, strictly smaller when the component escapes M.

Source: Aschbacher–Smith C.2.7, displayed (*) on printed p.146.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC
variable {G H : Type*} [Group G] [Finite G] [Group H]

theorem thompson_image_normalizer_control
    (R M : Subgroup G) (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (q : G →* H) (hq : Function.Surjective q) (hker : q.ker ≤ R) :
    normalizer ((elementaryAbelianMaxJ R).map q : Set H) ≤ M.map q := by
  rw [← normalizer_map_maxJ R q hq hker]
  exact map_mono ((normalizer_maxJ_le_characteristicNormalizerClosure R R
    (sSup_le fun _ hA => hA.1) le_rfl
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup R hR hne)).trans hcontrol)

theorem thompson_image_intersection_control
    (R M L : Subgroup G) (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hcontrol : R.characteristicNormalizerClosure ≤ M) (hout : ¬L ≤ M)
    (q : G →* H) (hq : Function.Surjective q) (hker : q.ker ≤ R) :
    L.map q ⊓ normalizer ((elementaryAbelianMaxJ R).map q : Set H) ≤
      (L ⊓ M).map q ∧ (L ⊓ M).map q < L.map q := by
  have hRM : R ≤ M := R.le_normalizer.trans
    ((normalizer_le_characteristicNormalizerClosure_self R hne).trans hcontrol)
  have hkerM := hker.trans hRM
  have himage := thompson_image_normalizer_control R M hR hne hcontrol q hq hker
  refine ⟨?_,lt_of_le_of_ne (map_mono inf_le_left) ?_⟩
  · rw [map_inf_of_ker_le q L M hkerM]
    exact inf_le_inf_left _ himage
  · intro he
    apply hout
    have hm : L.map q ≤ M.map q := by
      rw [←he]
      exact map_mono inf_le_right
    have hh := (map_le_iff_le_comap).mp hm
    rwa [comap_map_eq_self hkerM] at hh

end CFSG.Quasithin.ChapterC
