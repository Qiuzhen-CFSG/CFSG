module

public import Theory.GroupTheory.FourGroupNormalizerOvergroup
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.Mathieu.M22.Properties.FourNormalizers.FixedSylow
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads

/-!
# Strict characteristic-two overgroups of M₂₂ four-group normalizers

Every elementary four-group normal in an inner Sylow fixes a Witt hexad
pointwise. Its full normalizer lies strictly in that hexad's characteristic-two
stabilizer. For a Sylow of the full design group, intersect with its actual
normal M₂₂ subgroup. This is an inner Sylow, so a four-group lying in M₂₂ has
the same hexad placement. The full design normalizer and outer hexad stabilizer
then supply the required strict overgroup.

The finite coverage, normalizer containment, strictness, and characteristic-two
condition are proved in the imported descendants. No assertion is made about
four-groups outside M₂₂. This is the M₂₂ calculation used in the sporadic
paragraph of Aschbacher–Smith 15.3.43, printed p.1140, referring to 1.1.5(3)(f),
printed p.502, and GLS3 Table 5.3c.
-/

public section
namespace Sporadic.Mathieu.M22FourNormalizers
open Subgroup Theory.GroupTheory M22ValueBound.Concrete
open scoped Pointwise

/-- Every Sylow-normal four-group in M₂₂ has a strict characteristic-two
overgroup of its full normalizer. -/
theorem fourNormalizerOvergroups : FourNormalizerOvergroups M22 := by
  intro P V hVP hPV hV hc
  obtain ⟨B, hB, hVK⟩ := exists_hexad_kernel P V hVP hPV hV hc
  exact ⟨MulAction.stabilizer M22 B, normalizer_lt_hexad hB V hVK hV hc,
    hexad_characteristicTwo hB⟩

/-- The full design-group calculation for four-groups in the actual inner
M₂₂ subgroup; the Sylow and normalizer are both taken in the full design group. -/
theorem fourNormalizerOvergroupsIn :
    FourNormalizerOvergroupsIn M22ValueBound.Concrete.inner := by
  intro P V hVI hVP hPV hV hc
  obtain ⟨S, hS⟩ := P.exists_subgroupOf_eq_of_normal M22ValueBound.Concrete.inner
  let e : M22ValueBound.Concrete.inner ≃* M22 :=
    subgroupOfEquivOfLe M22_le_hexadDesignAut
  let R := V.subgroupOf M22ValueBound.Concrete.inner
  let W := R.map e.toMonoidHom
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRS : R ≤ (S : Subgroup M22ValueBound.Concrete.inner) := by
    rw [hS]
    exact comap_mono hVP
  have hSR : (S : Subgroup M22ValueBound.Concrete.inner) ≤
      normalizer (R : Set M22ValueBound.Concrete.inner) := by
    rw [hS]
    exact (comap_mono hPV).trans (le_normalizer_comap M22ValueBound.Concrete.inner.subtype)
  have hWQ : W ≤ (Q : Subgroup M22) := map_mono hRS
  have hQW : (Q : Subgroup M22) ≤ normalizer (W : Set M22) := by
    change (S : Subgroup M22ValueBound.Concrete.inner).map e.toMonoidHom ≤ _
    rw [show W = R.map e.toMonoidHom from rfl, ← map_equiv_normalizer_eq]
    exact map_mono hSR
  let := hV
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.subgroupOf hVI
  have hW : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  have hcW : Nat.card W = 4 :=
    (card_map_of_injective e.injective).trans
      ((Nat.card_congr (subgroupOfEquivOfLe hVI).toEquiv).trans hc)
  have hmap : W.map inclusion = V := by
    rw [show W = R.map e.toMonoidHom from rfl, map_map]
    change R.map M22ValueBound.Concrete.inner.subtype = V
    exact map_subgroupOf_eq_of_le hVI
  obtain ⟨B, hB, hWK⟩ := exists_hexad_kernel Q W hWQ hQW hW hcW
  refine ⟨MulAction.stabilizer m22DesignAut B, ?_, outer_hexad_characteristicTwo hB⟩
  rw [← hmap]
  exact outer_normalizer_lt_hexad hB W hWK hW hcW

end Sporadic.Mathieu.M22FourNormalizers
